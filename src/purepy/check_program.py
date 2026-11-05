"""Module discovery and checking of a program by the generated type checker"""

import pathlib
from dataclasses import dataclass

from purepy_conformance import TYPE_CHECKER_VERDICT, Classification, Exit, PurePyOutcome

from . import syntax
from .generated import Finite_Map, Option, Programs, Syntax
from .messages import classification, message, position
from .rules import rule
from .syntax import ModuleBody, Name, Program, Reason, parse_name

MAIN = parse_name("__main__")


def module_path(q: Name, base_dir: pathlib.Path) -> pathlib.Path:
    stem = pathlib.Path(*Syntax.variables(q))
    for candidate in (base_dir / f"{stem}.py", base_dir / stem / "__init__.py"):
        if candidate.exists():
            return candidate
    assert (base_dir / stem).is_dir()
    return base_dir / stem


def module_name(base_dir: pathlib.Path, path: pathlib.Path) -> Name | None:
    rel = path.relative_to(base_dir)
    parts = rel.parent.parts if rel.name == "__init__.py" else rel.with_suffix("").parts
    return parse_name(".".join(parts)) if len(parts) > 0 else None


def module_names(base_dir: pathlib.Path) -> set[Name]:
    names = {
        module_name(base_dir, p) for p in base_dir.rglob("*.py") if "__pycache__" not in p.parts
    }
    return {p for q in names if q is not None for p in [q, *Syntax.proper_prefixes(q)]}


type PurePyRejects = Programs.IllFormed | syntax.ParserRejects


def parse_program(entry_path: pathlib.Path) -> Program:
    """Entry module parsed first, so its errors take precedence"""
    base_dir = entry_path.parent
    names = sorted(module_names(base_dir), key=Syntax.variables)
    return program(
        {
            MAIN: parse_module(MAIN, entry_path),
            **{q: parse_module(q, module_path(q, base_dir)) for q in names},
        }
    )


def parse_module(q: Name, path: pathlib.Path) -> ModuleBody:
    """A package directory is an empty module"""
    try:
        return syntax.parse_module("" if path.is_dir() else path.read_text(), str(path), q)
    except syntax.ParserRejects as e:
        e.module = q
        raise


def program(bodies: dict[Name, ModuleBody]) -> Program:
    return Finite_Map.fmap_of_list(list(bodies.items()))


def check(M: Program) -> Programs.IllFormed | None:
    match Programs.check_program(M):
        case Option.None_():
            return None
        case Option.Some(Programs.IllFormed() as f):
            return f
        case result:
            raise AssertionError(f"unexpected result: {result}")


@dataclass(frozen=True)
class Diagnostic:
    """Rejection of a program, classified as in the taxonomy of the specification"""

    outcome: PurePyOutcome
    module: Name | None  # None for the entry module
    position: tuple[int, int | None] | None
    message: str
    rule: str | None  # rule of the specification violated, as the conformance suite cites it


def reason_outcome(r: Reason) -> PurePyOutcome:
    excluded = classification(r) == Classification.FOR_NOW
    return PurePyOutcome.EXCLUDED_FOR_NOW if excluded else PurePyOutcome.TYPING_REJECTS


def diagnostic(rejection: PurePyRejects) -> Diagnostic:
    """Rule cited only for a typing rejection, as in the conformance suite"""
    match rejection:
        case syntax.ParserRejects(module=q, line=line, col=col, msg=msg, classification=k):
            excluded = k == Classification.FOR_NOW
            outcome = PurePyOutcome.EXCLUDED_FOR_NOW if excluded else PurePyOutcome.PARSER_REJECTS
            return Diagnostic(outcome, q, None if line is None else (line, col), msg, None)
        case Programs.IllFormed(q, r):
            outcome = reason_outcome(r)
            cited = rule(r) if outcome == PurePyOutcome.TYPING_REJECTS else None
            return Diagnostic(outcome, q, position(r), message(r), cited)
        case _:
            raise AssertionError(f"unexpected rejection: {rejection}")


def check_program(entry_path: pathlib.Path) -> Diagnostic | None:
    try:
        rejection = check(parse_program(entry_path))
    except syntax.ParserRejects as e:
        rejection = e
    return None if rejection is None else diagnostic(rejection)


def check_module(path: pathlib.Path) -> Diagnostic | None:
    """Check the module at path as a program of one module"""
    try:
        rejection = check(program({MAIN: parse_module(MAIN, path)}))
    except syntax.ParserRejects as e:
        rejection = e
    return None if rejection is None else diagnostic(rejection)


def exit_code(d: Diagnostic | None) -> Exit:
    return Exit.OK if d is None else TYPE_CHECKER_VERDICT[d.outcome][0]


def error_path(d: Diagnostic, entry_path: pathlib.Path) -> pathlib.Path:
    """File of the module at fault"""
    q = d.module
    return entry_path if q is None or q == MAIN else module_path(q, entry_path.parent)


def format_diagnostic(d: Diagnostic | None, entry_path: pathlib.Path) -> str:
    if d is None:
        return f"{entry_path}: ok"
    path = error_path(d, entry_path)
    where = str(path) if d.position is None else f"{path}:{d.position[0]}:{d.position[1]}"
    cited = "" if d.rule is None else f", rule {d.rule}"
    return f"{where}: {d.message} [{d.outcome}{cited}]"

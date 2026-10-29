"""Module discovery and checking of a program by the generated type checker"""

import pathlib
from typing import Any

from . import syntax
from .conformance import Exit
from .generated import Finite_Map, Option, Programs, Reasons
from .messages import message
from .syntax import name
from .type_syntax import Name, parse_name, proper_prefixes

MAIN = parse_name("__main__")


def module_path(q: Name, base_dir: pathlib.Path) -> pathlib.Path:
    stem = pathlib.Path(*q.parts)
    for candidate in (base_dir / f"{stem}.py", base_dir / stem / "__init__.py"):
        if candidate.exists():
            return candidate
    assert (base_dir / stem).is_dir()
    return base_dir / stem


def module_name(base_dir: pathlib.Path, path: pathlib.Path) -> Name | None:
    rel = path.relative_to(base_dir)
    parts = rel.parent.parts if rel.name == "__init__.py" else rel.with_suffix("").parts
    return Name(parts) if len(parts) > 0 else None


def module_names(base_dir: pathlib.Path) -> set[Name]:
    names = {
        module_name(base_dir, p) for p in base_dir.rglob("*.py") if "__pycache__" not in p.parts
    }
    return {p for q in names if q is not None for p in [q, *proper_prefixes(q)]}


# Entry module parsed first, so its errors take precedence
def parse_program(entry_path: pathlib.Path) -> Any:
    base_dir = entry_path.parent
    names = sorted(module_names(base_dir), key=str)
    return program(
        {
            MAIN: parse_module(MAIN, entry_path),
            **{q: parse_module(q, module_path(q, base_dir)) for q in names},
        }
    )


# A package directory is an empty module
def parse_module(q: Name, path: pathlib.Path) -> Any:
    try:
        return syntax.parse_module("" if path.is_dir() else path.read_text(), str(path), q)
    except syntax.Unsupported as e:
        e.module = q
        raise


def program(bodies: dict[Name, Any]) -> Any:
    return Finite_Map.fmap_of_list([(name(q), body) for q, body in bodies.items()])


# Module and reason of an ill-formed program, or None
def check(M: Any) -> tuple[Any, Any] | None:
    match Programs.check_program(M):
        case Option.None_():
            return None
        case Option.Some((q, r)):
            return (q, r)
        case result:
            raise AssertionError(f"unexpected result: {result}")


type Result = tuple[Any, Any] | syntax.Unsupported | None


def check_program(entry_path: pathlib.Path) -> Result:
    try:
        return check(parse_program(entry_path))
    except syntax.Unsupported as e:
        return e


# Check the module at path as a program of one module
def check_module(path: pathlib.Path) -> Result:
    try:
        return check(program({MAIN: parse_module(MAIN, path)}))
    except syntax.Unsupported as e:
        return e


def exit_code(result: Result) -> Exit:
    match result:
        case None:
            return Exit.OK
        case syntax.Unsupported():
            return Exit(result.exit_code)
        case (_, Reasons.ImportCycle()):
            return Exit.ILL_FORMED_PROGRAM
        case _:
            return Exit.ILL_FORMED


# File of the module at fault, or of the entry module for a program-level error
def error_path(result: Result, entry_path: pathlib.Path) -> pathlib.Path:
    match result:
        case syntax.Unsupported():
            q = result.module
        case ((x, xs), r) if not isinstance(r, Reasons.ImportCycle):
            q = Name((x, *xs))
        case _:
            q = None
    return entry_path if q is None or q == MAIN else module_path(q, entry_path.parent)


def format_result(result: Result, filename: str) -> str:
    match result:
        case None:
            return f"{filename}: ok"
        case syntax.Unsupported():
            return syntax.format_result(result, filename)
        case (_, Reasons.Located((line, col), r)):
            return f"{filename}:{line}:{col}: {message(r)}"
        case (_, r):
            return f"{filename}: {message(r)}"


def format_program_result(result: Result, entry_path: pathlib.Path) -> str:
    return format_result(result, str(error_path(result, entry_path)))

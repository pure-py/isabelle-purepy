"""Module discovery and checking of a program by the generated type checker"""

import pathlib
from typing import Any

from . import syntax
from .generated import Finite_Map, Option, Programs, Reasons
from .messages import IllFormed, IllFormedModule, IllFormedProgram, message
from .messages import name as name_of
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


# Entry module parsed first, so that its errors take precedence
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


def ill_formed(q: Any, r: Any) -> IllFormed:
    """Failure for reason r in module q"""
    match r:
        case Reasons.ImportCycle():
            return IllFormedProgram(message(r))
        case Reasons.Located(p, r_):
            return IllFormedModule(p, message(r_), name_of(q))
        case _:
            return IllFormedModule(None, message(r), name_of(q))


def check(M: Any) -> IllFormed | None:
    match Programs.check_program(M):
        case Option.None_():
            return None
        case Option.Some((q, r)):
            return ill_formed(q, r)
        case result:
            raise AssertionError(f"unexpected result: {result}")


def check_program(entry_path: pathlib.Path) -> IllFormed | syntax.Unsupported | None:
    try:
        return check(parse_program(entry_path))
    except syntax.Unsupported as e:
        return e


# Check the module at path as a program of one module
def check_module(path: pathlib.Path) -> IllFormed | syntax.Unsupported | None:
    try:
        return check(program({MAIN: parse_module(MAIN, path)}))
    except syntax.Unsupported as e:
        return e


# File of the module at fault, or of the entry module for a program-level error
def error_path(result: IllFormed | syntax.Unsupported, entry_path: pathlib.Path) -> pathlib.Path:
    q = result.module if isinstance(result, (IllFormedModule, syntax.Unsupported)) else None
    return entry_path if q is None or q == MAIN else module_path(q, entry_path.parent)


def format_result(result: IllFormed | syntax.Unsupported | None, filename: str) -> str:
    match result:
        case syntax.Unsupported():
            return syntax.format_result(result, filename)
        case None:
            return f"{filename}: ok"
        case IllFormedModule():
            return f"{filename}:{result.line}:{result.col}: {result.msg}"
        case _:
            return f"{filename}: {result.msg}"


def format_program_result(
    result: IllFormed | syntax.Unsupported | None, entry_path: pathlib.Path
) -> str:
    path = entry_path if result is None else error_path(result, entry_path)
    return format_result(result, str(path))

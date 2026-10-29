"""Module discovery and checking of a program by the generated type checker"""

import ast
import pathlib
from typing import Any

from . import syntax
from .generated import Finite_Map, Option, Programs, Reasons
from .messages import IllFormed, IllFormedModule, IllFormedProgram, message
from .messages import name as name_of
from .translate import module_body, name
from .type_syntax import Name, parse_name, proper_prefixes

MAIN = parse_name("__main__")


def module_path(q: Name, base_dir: pathlib.Path) -> pathlib.Path:
    stem = pathlib.Path(*q.parts)
    for candidate in (base_dir / f"{stem}.py", base_dir / stem / "__init__.py"):
        if candidate.exists():
            return candidate
    assert (base_dir / stem).is_dir()
    return base_dir / stem


def parse(path: pathlib.Path) -> ast.Module:
    if path.is_dir():
        return ast.Module(body=[], type_ignores=[])
    source = path.read_text()
    try:
        m = syntax.parse(source, str(path))
    except SyntaxError as e:
        raise syntax.ParseError(e) from e
    unsupported = syntax.check_syntax_module(m)
    if unsupported is not None:
        raise unsupported
    return m


def module_name(base_dir: pathlib.Path, path: pathlib.Path) -> Name | None:
    rel = path.relative_to(base_dir)
    parts = rel.parent.parts if rel.name == "__init__.py" else rel.with_suffix("").parts
    return Name(parts) if len(parts) > 0 else None


def module_names(base_dir: pathlib.Path) -> set[Name]:
    names = {
        module_name(base_dir, p) for p in base_dir.rglob("*.py") if "__pycache__" not in p.parts
    }
    return {p for q in names if q is not None for p in [q, *proper_prefixes(q)]}


def parse_program(entry_path: pathlib.Path) -> dict[Name, ast.Module]:
    """Modules by name, every module of the source tree parsed, the main module first"""
    base_dir = entry_path.parent
    names = sorted(module_names(base_dir), key=str)
    return {
        MAIN: parse_module(MAIN, entry_path),
        **{q: parse_module(q, module_path(q, base_dir)) for q in names},
    }


def parse_module(q: Name, path: pathlib.Path) -> ast.Module:
    try:
        return parse(path)
    except syntax.Unsupported as e:
        e.module = q
        raise


def translate_program(M: dict[Name, ast.Module]) -> Any:
    return Finite_Map.fmap_of_list([(name(q), module_body(q, m)) for q, m in M.items()])


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
        return check(translate_program(parse_program(entry_path)))
    except syntax.Unsupported as e:
        return e


# Check the module at path as a program of one module
def check_module(path: pathlib.Path) -> IllFormed | syntax.Unsupported | None:
    try:
        return check(translate_program({MAIN: parse_module(MAIN, path)}))
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

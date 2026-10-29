import ast
from itertools import dropwhile, takewhile

from .type_syntax import (
    TypeExpr,
    Var,
    parse_annotation,
    parse_name,
    root,
)

# PurePy statement: Python statement, mutual def region or mutual type region. Python body (statement
# list) represents spec's right-nested sequence s s'.
type TypeDefinition = ast.ClassDef | ast.TypeAlias
type Statement = ast.stmt | list[ast.FunctionDef] | list[TypeDefinition]


def is_import(s: ast.stmt) -> bool:
    return isinstance(s, (ast.Import, ast.ImportFrom))


def split_imports(body: list[ast.stmt]) -> tuple[list[ast.stmt], list[ast.stmt]]:
    return list(takewhile(is_import, body)), list(dropwhile(is_import, body))


def statements(body: list[ast.stmt]) -> list[Statement]:
    if len(body) == 0:
        return []
    head = body[0]
    rest = body[1:]
    if isinstance(head, ast.FunctionDef):
        return extend_def_region([head], rest)
    if isinstance(head, (ast.ClassDef, ast.TypeAlias)):
        return extend_type_region([head], rest)
    return [head] + statements(rest)


def extend_def_region(region: list[ast.FunctionDef], rest: list[ast.stmt]) -> list[Statement]:
    if len(rest) == 0:
        return [region]
    head = rest[0]
    if isinstance(head, ast.FunctionDef):
        return extend_def_region(region + [head], rest[1:])
    return [region] + statements(rest)


def extend_type_region(region: list[TypeDefinition], rest: list[ast.stmt]) -> list[Statement]:
    if len(rest) == 0:
        return [region]
    head = rest[0]
    if isinstance(head, (ast.ClassDef, ast.TypeAlias)):
        return extend_type_region(region + [head], rest[1:])
    return [region] + statements(rest)


def bound(pattern: ast.pattern) -> list[Var]:
    """Variables bound by pattern, in order and with repetitions"""
    match pattern:
        case ast.MatchValue() | ast.MatchSingleton():
            return []
        case ast.MatchAs(pattern=p, name=x):
            return (bound(p) if p is not None else []) + ([x] if x else [])
        case ast.MatchSequence(patterns=ps) | ast.MatchMapping(patterns=ps):
            return [x for p in ps for x in bound(p)]
        case ast.MatchClass(patterns=ps, kwd_patterns=ps_):
            return [x for p in list(ps) + list(ps_) for x in bound(p)]
        case _:
            raise AssertionError(f"unexpected pattern: {type(pattern).__name__}")


def dict_keys(e: ast.Dict) -> list[ast.expr]:
    keys = [k for k in e.keys if k is not None]
    assert len(keys) == len(e.keys)
    return keys


def target_name(g: ast.comprehension) -> str:
    assert isinstance(g.target, ast.Name)
    return g.target.id


def declares(s: ast.stmt) -> list[tuple[Var, ast.stmt]]:
    """Names declared in `s`, or bound by import `s`, with their AST nodes, in textual order and
    with repeats."""
    match s:
        case ast.AnnAssign():
            assert isinstance(s.target, ast.Name)
            return [(s.target.id, s)]
        case ast.If(body=ss, orelse=ss_):
            return declares_body(ss) + declares_body(ss_)
        case ast.Match():
            return [d for case in s.cases for d in declares_body(case.body)]
        case ast.FunctionDef(name=x) | ast.ClassDef(name=x) | ast.TypeAlias(name=ast.Name(id=x)):
            return [(x, s)]
        case ast.Import():
            (alias,) = s.names
            return [(root(parse_name(alias.name)), s)]
        case ast.ImportFrom():
            return [(alias.name, s) for alias in s.names]
        case _:
            return []


def declares_body(body: list[ast.stmt]) -> list[tuple[Var, ast.stmt]]:
    return [d for s in body for d in declares(s)]


def type_param_names(node: ast.FunctionDef | ast.ClassDef | ast.TypeAlias) -> tuple[Var, ...]:
    alphas = tuple(p.name for p in node.type_params if isinstance(p, ast.TypeVar))
    assert len(alphas) == len(node.type_params)
    return alphas


def own_fields(node: ast.ClassDef) -> tuple[tuple[Var, TypeExpr], ...]:
    return tuple(
        (t.target.id, type_expr(t.annotation))
        for t in node.body
        if isinstance(t, ast.AnnAssign) and isinstance(t.target, ast.Name)
    )


def type_expr(annotation: ast.expr | None) -> TypeExpr:
    assert annotation is not None
    t = parse_annotation(annotation)
    assert t is not None
    return t

from __future__ import annotations

import ast
from collections.abc import Sequence
from dataclasses import dataclass
from enum import Enum
from types import EllipsisType


class Primitive(Enum):
    OBJECT = "object"
    NEVER = "Never"
    NONE = "None"
    BOOL = "bool"
    INT = "int"
    FLOAT = "float"
    STR = "str"
    SIZED = "Sized"


class TypeConstructor(Enum):
    LIST = "list"
    TUPLE = "tuple"
    DICT = "dict"
    CALLABLE = "Callable"
    LITERAL = "Literal"


type Var = str


@dataclass(frozen=True)
class Name:
    parts: tuple[Var, ...]

    def __str__(self) -> str:
        return ".".join(self.parts)


def parse_name(name: str) -> Name:
    return Name(tuple(name.split(".")))


def qualified(q: Name, x: Var) -> Name:
    return Name(q.parts + (x,))


def root(q: Name) -> Var:
    return q.parts[0]


def parent(q: Name) -> Name | None:
    return Name(q.parts[:-1]) if len(q.parts) > 1 else None


def proper_prefixes(q: Name) -> list[Name]:
    return [Name(q.parts[:i]) for i in range(1, len(q.parts))]


@dataclass(frozen=True, eq=False)
class Literal:
    """Equality compares the value's Python type as well, since True == 1 and 1 == 1.0
    hold between values of different types."""

    value: int | float | str | bool | None

    def __eq__(self, other: object) -> bool:
        return (
            isinstance(other, Literal)
            and type(self.value) is type(other.value)
            and self.value == other.value
        )

    def __hash__(self) -> int:
        return hash((type(self.value).__name__, self.value))


def float_literal(ell: Literal) -> bool:
    return isinstance(ell.value, float)


@dataclass(frozen=True)
class LiteralType:
    ell: Literal

    def __post_init__(self) -> None:
        assert not float_literal(self.ell)


@dataclass(frozen=True)
class ListExpr:
    elem: TypeExpr


@dataclass(frozen=True)
class TupleExpr:
    components: tuple[TypeExpr, ...]


@dataclass(frozen=True)
class DictExpr:
    value: TypeExpr


@dataclass(frozen=True)
class CallableExpr:
    params: tuple[TypeExpr, ...]
    result: TypeExpr


@dataclass(frozen=True)
class TypeName:
    q: Name
    args: tuple[TypeExpr, ...]


@dataclass(frozen=True)
class UnionExpr:
    left: TypeExpr
    right: TypeExpr


type TypeExpr = (
    Primitive | ListExpr | TupleExpr | DictExpr | CallableExpr | LiteralType | TypeName | UnionExpr
)


def parse_annotation(e: ast.expr) -> TypeExpr | None:
    match e:
        case ast.Constant(value=None):
            return Primitive.NONE
        case ast.Name(id=x):
            return next(
                (nu for nu in Primitive if nu.value == x),
                TypeName(Name((x,)), ()),
            )
        case ast.Attribute():
            q = dotted_name(e)
            return None if q is None else TypeName(q, ())
        case ast.BinOp(op=ast.BitOr()):
            return union(parse_annotation(e.left), parse_annotation(e.right))
        case ast.Subscript():
            return parse_subscript(e)
        case _:
            return None


def dotted_name(e: ast.expr) -> Name | None:
    match e:
        case ast.Name(id=x):
            return Name((x,))
        case ast.Attribute(value=e_, attr=x):
            q = dotted_name(e_)
            return None if q is None else qualified(q, x)
        case _:
            return None


def parse_subscript(e: ast.Subscript) -> TypeExpr | None:
    head = e.value.id if isinstance(e.value, ast.Name) else None
    indices = subscript_args(e.slice)
    if head == TypeConstructor.LITERAL.value:
        return literal_type(indices[0]) if len(indices) == 1 else None
    if head == TypeConstructor.CALLABLE.value:
        return parse_callable(indices)
    args = parse_annotations(indices)
    if args is None:
        return None
    if head == TypeConstructor.LIST.value:
        return ListExpr(args[0]) if len(args) == 1 else None
    if head == TypeConstructor.TUPLE.value:
        return TupleExpr(args)
    if head == TypeConstructor.DICT.value:
        return DictExpr(args[1]) if len(args) == 2 and args[0] == Primitive.STR else None
    q = dotted_name(e.value)
    return None if q is None else TypeName(q, args)


def literal(e: ast.expr) -> Literal | None:
    match e:
        case ast.Constant(value=v):
            return None if isinstance(v, (bytes, complex, EllipsisType)) else Literal(v)
        case _:
            return None


def literal_type(e: ast.expr) -> LiteralType | None:
    ell = literal(e)
    return None if ell is None or float_literal(ell) else LiteralType(ell)


def parse_callable(args: tuple[ast.expr, ...]) -> TypeExpr | None:
    if len(args) != 2 or not isinstance(args[0], ast.List):
        return None
    params = parse_annotations(args[0].elts)
    result = parse_annotation(args[1])
    return None if params is None or result is None else CallableExpr(params, result)


def subscript_args(s: ast.expr) -> tuple[ast.expr, ...]:
    return tuple(s.elts) if isinstance(s, ast.Tuple) else (s,)


def parse_annotations(es: Sequence[ast.expr]) -> tuple[TypeExpr, ...] | None:
    psis = tuple(parse_annotation(e) for e in es)
    return (
        None if any(psi is None for psi in psis) else tuple(psi for psi in psis if psi is not None)
    )


def union(psi: TypeExpr | None, psi_: TypeExpr | None) -> TypeExpr | None:
    return None if psi is None or psi_ is None else UnionExpr(psi, psi_)

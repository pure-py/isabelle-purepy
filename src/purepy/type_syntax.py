import ast
from dataclasses import dataclass

type Var = str


@dataclass(frozen=True)
class Name:
    parts: tuple[Var, ...]

    def __str__(self) -> str:
        return ".".join(self.parts)


def parse_name(name: str) -> Name:
    return Name(tuple(name.split(".")))


def root(q: Name) -> Var:
    return q.parts[0]


def proper_prefixes(q: Name) -> list[Name]:
    return [Name(q.parts[:i]) for i in range(1, len(q.parts))]


def dotted_name(e: ast.expr) -> Name | None:
    match e:
        case ast.Name(id=x):
            return Name((x,))
        case ast.Attribute(value=e_, attr=x):
            q = dotted_name(e_)
            return None if q is None else Name((*q.parts, x))
        case _:
            return None

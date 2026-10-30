"""Wrap the located arguments of generated syntax and value constructors at position (0, 0)"""

import dataclasses
import functools

from purepy.generated import Contexts, Option, Positions, Semantics, Syntax

LOCATED = {
    "ExprVar",
    "ExprLiteral",
    "ExprCall",
    "ExprDict",
    "ExprAttribute",
    "ExprSubscript",
    "ExprBinOp",
    "ExprUnOp",
    "ExprAnd",
    "ExprOr",
    "ExprCond",
    "ExprList",
    "ExprTuple",
    "ExprListComp",
    "ExprDictComp",
    "ExprLambda",
    "Guard",
    "Generator",
    "PatLiteral",
    "PatVar",
    "PatWildcard",
    "PatList",
    "PatTuple",
    "PatConstr",
    "PatDict",
    "PatAs",
    "StmtPass",
    "StmtSeq",
    "StmtDeclare",
    "StmtAssign",
    "StmtExpr",
    "StmtAssert",
    "StmtReturn",
    "StmtIf",
    "StmtMatch",
    "StmtMutualRegion",
    "Def",
    "Dataclass",
    "TypeStmt",
    "Import",
    "FromImport",
}
LOCATED_CLASSES = tuple(getattr(Syntax, n, None) or getattr(Syntax, n + "_") for n in LOCATED)


def wrap(x):
    if isinstance(x, LOCATED_CLASSES):
        return Positions.At((0, 0), x)
    if isinstance(x, Option.Some):
        return Option.Some(wrap(getattr(x, dataclasses.fields(x)[0].name)))
    if isinstance(x, list):
        return [wrap(y) for y in x]
    if isinstance(x, tuple):
        return tuple(wrap(y) for y in x)
    return x


def install(module):
    for cls in vars(module).values():
        if isinstance(cls, type) and hasattr(cls, "__dataclass_fields__"):
            init = cls.__init__

            @functools.wraps(init)
            def wrapped(self, *args, _init=init):
                _init(self, *map(wrap, args))

            cls.__init__ = wrapped


for module in (Syntax, Semantics, Contexts):
    install(module)

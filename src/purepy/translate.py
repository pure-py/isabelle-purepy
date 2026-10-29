"""Translation of parsed modules into the generated syntax"""

import ast
from functools import reduce
from typing import Any

from . import syntax
from .generated import Option, Positions, Syntax
from .syntax_utils import (
    Statement,
    dict_keys,
    own_fields,
    split_imports,
    statements,
    target_name,
    type_expr,
    type_param_names,
)
from .type_syntax import (
    CallableExpr,
    DictExpr,
    ListExpr,
    LiteralType,
    Name,
    Primitive,
    TupleExpr,
    TypeExpr,
    TypeName,
    UnionExpr,
    dotted_name,
    parse_name,
)


def lit(v: object) -> Any:
    match v:
        case bool():
            return Syntax.LitBool(v)
        case int():
            return Syntax.LitInt(v)
        case float():
            return Syntax.LitFloat(v)
        case str():
            return Syntax.LitString(v)
        case None:
            return Syntax.LitNone()
        case _:
            raise AssertionError(f"unexpected literal: {type(v).__name__}")


def name(q: Name) -> Any:
    return (q.parts[0], list(q.parts[1:]))


def option(x: Any) -> Any:
    return Option.None_() if x is None else Option.Some(x)


def position(node: ast.expr | ast.stmt | ast.pattern) -> tuple[int, int]:
    return (node.lineno, node.col_offset)


def at(node: ast.expr | ast.stmt | ast.pattern, term: Any) -> Any:
    """Term located at node"""
    return Positions.At(position(node), term)


def located_at(t: Any) -> tuple[int, int]:
    match t:
        case Positions.At((line, col), _):
            return (line, col)
        case _:
            raise AssertionError(f"unlocated term: {t}")


def node(t: Any) -> Any:
    match t:
        case Positions.At(_, u):
            return u
        case _:
            raise AssertionError(f"unlocated term: {t}")


PRIM_TY = {
    Primitive.OBJECT: Syntax.object_,
    Primitive.NEVER: Syntax.Never,
    Primitive.NONE: Syntax.NoneType,
    Primitive.BOOL: Syntax.bool_,
    Primitive.INT: Syntax.int_,
    Primitive.FLOAT: Syntax.float_,
    Primitive.STR: Syntax.str_,
    Primitive.SIZED: Syntax.Sized,
}


def ty_expr(psi: TypeExpr) -> Any:
    match psi:
        case Primitive():
            return Syntax.TyExprPrim(PRIM_TY[psi]())
        case ListExpr(elem):
            return Syntax.TyExprList(ty_expr(elem))
        case TupleExpr(components):
            return Syntax.TyExprTuple([ty_expr(c) for c in components])
        case DictExpr(value):
            return Syntax.TyExprDict(ty_expr(value))
        case CallableExpr(params, result):
            return Syntax.TyExprCallable([ty_expr(q) for q in params], ty_expr(result))
        case LiteralType(ell):
            return Syntax.TyExprLiteral(lit(ell.value))
        case TypeName(q, args):
            return Syntax.TyExprName(name(q), [ty_expr(a) for a in args])
        case UnionExpr(left, right):
            return Syntax.TyExprUnion(ty_expr(left), ty_expr(right))


def annotation(e: ast.expr | None) -> Any:
    assert e is not None  # missing annotations rejected by the parser
    return ty_expr(type_expr(e))


BOP: dict[type[ast.operator | ast.cmpop], Any] = {
    ast.BitOr: Syntax.BOpBitOr,
    ast.Eq: Syntax.BOpEq,
    ast.NotEq: Syntax.BOpNeq,
    ast.Lt: Syntax.BOpLt,
    ast.LtE: Syntax.BOpLeq,
    ast.Gt: Syntax.BOpGt,
    ast.GtE: Syntax.BOpGeq,
    ast.Add: Syntax.BOpAdd,
    ast.Sub: Syntax.BOpSub,
    ast.Mult: Syntax.BOpMul,
    ast.Div: Syntax.BOpDiv,
    ast.FloorDiv: Syntax.BOpFloorDiv,
    ast.Mod: Syntax.BOpMod,
    ast.Pow: Syntax.BOpPow,
    ast.In: Syntax.BOpIn,
    ast.NotIn: Syntax.BOpNotIn,
}

UOP: dict[type[ast.unaryop], Any] = {
    ast.Not: Syntax.UOpNot,
    ast.UAdd: Syntax.UOpPos,
    ast.USub: Syntax.UOpNeg,
}


def expr(e: ast.expr) -> Any:
    return at(e, expr_node(e))


def expr_node(e: ast.expr) -> Any:
    match e:
        case ast.Name(id=x):
            return Syntax.ExprVar(x)
        case ast.Constant(value=v):
            return Syntax.ExprLiteral(lit(v))
        case ast.Call(func=f, args=es, keywords=ks):
            return Syntax.ExprCall(expr(f), ([expr(e_) for e_ in es], [keyword(k) for k in ks]))
        case ast.Dict(values=vs):
            return Syntax.ExprDict([(expr(k), expr(v)) for k, v in zip(dict_keys(e), vs)])
        case ast.Attribute(value=e_, attr=x):
            return Syntax.ExprAttribute(expr(e_), x)
        case ast.Subscript(value=e_, slice=e__):
            return Syntax.ExprSubscript(expr(e_), expr(e__))
        case ast.BinOp(left=e_, op=op, right=e__):
            return Syntax.ExprBinOp(BOP[type(op)](), expr(e_), expr(e__))
        case ast.Compare(left=e_, ops=[op], comparators=[e__]):
            return Syntax.ExprBinOp(BOP[type(op)](), expr(e_), expr(e__))
        case ast.UnaryOp(op=op, operand=e_):
            return Syntax.ExprUnOp(UOP[type(op)](), expr(e_))
        case ast.BoolOp(op=ast.And(), values=[e_, e__]):
            return Syntax.ExprAnd(expr(e_), expr(e__))
        case ast.BoolOp(op=ast.Or(), values=[e_, e__]):
            return Syntax.ExprOr(expr(e_), expr(e__))
        case ast.IfExp(test=e_, body=e1, orelse=e2):
            return Syntax.ExprCond(expr(e1), expr(e_), expr(e2))
        case ast.List(elts=es):
            return Syntax.ExprList([expr(e_) for e_ in es])
        case ast.Tuple(elts=es):
            return Syntax.ExprTuple([expr(e_) for e_ in es])
        case ast.ListComp(elt=e_, generators=gs):
            return Syntax.ExprListComp(expr(e_), qualifiers(gs))
        case ast.DictComp(key=e_, value=e__, generators=gs):
            return Syntax.ExprDictComp(expr(e_), expr(e__), qualifiers(gs))
        case ast.Lambda(args=args, body=e_):
            return Syntax.ExprLambda([a.arg for a in args.args], expr(e_))
        case _:
            raise AssertionError(f"unexpected expression: {type(e).__name__}")


def keyword(k: ast.keyword) -> tuple[Any, Any]:
    assert k.arg is not None  # dictionary unpacking rejected by the parser
    return (k.arg, expr(k.value))


# A generator is located at its target, since the parsed form has no position for the generator itself
def qualifiers(gs: list[ast.comprehension]) -> list[Any]:
    return [
        q
        for g in gs
        for q in [
            at(g.target, Syntax.Generator(target_name(g), expr(g.iter))),
            *(at(c, Syntax.Guard(expr(c))) for c in g.ifs),
        ]
    ]


def pat(p: ast.pattern) -> Any:
    return at(p, pat_node(p))


def pat_node(p: ast.pattern) -> Any:
    match p:
        case ast.MatchValue(value=ast.Constant(value=v)) | ast.MatchSingleton(value=v):
            return Syntax.PatLiteral(lit(v))
        case ast.MatchAs(pattern=None, name=None):
            return Syntax.PatWildcard()
        case ast.MatchAs(pattern=None, name=str(x)):
            return Syntax.PatVar(x)
        case ast.MatchAs(pattern=ast.pattern() as p_, name=str(x)):
            return Syntax.PatAs(pat(p_), x)
        case syntax.PatList(patterns=ps):
            return Syntax.PatList([pat(p_) for p_ in ps])
        case syntax.PatTuple(patterns=ps):
            return Syntax.PatTuple([pat(p_) for p_ in ps])
        case ast.MatchClass(cls=c, patterns=ps, kwd_attrs=xs, kwd_patterns=qs):
            q = dotted_name(c)
            assert q is not None  # other heads rejected by Python
            return Syntax.PatConstr(
                name(q), ([pat(p_) for p_ in ps], [(x, pat(q_)) for x, q_ in zip(xs, qs)])
            )
        case ast.MatchMapping(keys=ks, patterns=ps):
            return Syntax.PatDict([(key(k), pat(q)) for k, q in zip(ks, ps)])
        case _:
            raise AssertionError(f"unexpected pattern: {type(p).__name__}")


def key(k: ast.expr) -> str:
    assert isinstance(k, ast.Constant) and isinstance(k.value, str)  # others rejected by the parser
    return k.value


def stmt(s: ast.stmt) -> Any:
    return at(s, stmt_node(s))


def stmt_node(s: ast.stmt) -> Any:
    match s:
        case ast.Pass():
            return Syntax.StmtPass()
        case ast.Assign(targets=[ast.Name(id=x)], value=e):
            return Syntax.StmtAssign(x, Option.None_(), expr(e))
        case ast.AnnAssign(target=ast.Name(id=x), annotation=a, value=None):
            return Syntax.StmtDeclare(x, annotation(a))
        case ast.AnnAssign(target=ast.Name(id=x), annotation=a, value=ast.expr() as e):
            return Syntax.StmtAssign(x, Option.Some(annotation(a)), expr(e))
        case ast.Expr(value=e):
            return Syntax.StmtExpr(expr(e))
        case ast.Assert(test=e, msg=e_):
            return Syntax.StmtAssert(expr(e), option(None if e_ is None else expr(e_)))
        case ast.Return(value=e):
            return Syntax.StmtReturn(option(None if e is None else expr(e)))
        case ast.If(test=e, body=ss, orelse=ss_):
            elifs, else_ = branches(s.col_offset, ss_)
            return Syntax.StmtIf(expr(e), seq(ss), elifs, else_)
        case ast.Match(subject=e, cases=bs):
            return Syntax.StmtMatch(expr(e), [(pat(b.pattern), seq(b.body)) for b in bs])
        case _:
            raise AssertionError(f"unexpected statement: {type(s).__name__}")


def branches(col: int, orelse: list[ast.stmt]) -> tuple[list[Any], Any]:
    """Recover the elifs, which Python parses as nested ifs. A nested if at the same column as the
    outer if is an elif."""
    match orelse:
        case []:
            return [], Option.None_()
        case [ast.If(test=e, body=ss, orelse=ss_) as s] if s.col_offset == col:
            elifs, else_ = branches(col, ss_)
            return [(expr(e), seq(ss)), *elifs], else_
        case _:
            return [], Option.Some(seq(orelse))


def seq(body: list[ast.stmt]) -> Any:
    *items, item = statements(body)
    return reduce(lambda s, item_: seq_stmt(item_stmt(item_), s), reversed(items), item_stmt(item))


# Sequence at the position of its first statement
def seq_stmt(s: Any, s_: Any) -> Any:
    return Positions.At(located_at(s), Syntax.StmtSeq(s, s_))


def item_stmt(item: Statement) -> Any:
    match item:
        case ast.stmt():
            return stmt(item)
        case [ast.FunctionDef() as d, *_]:
            return at(d, Syntax.StmtMutualRegion([func(d_) for d_ in item]))
        case _:
            raise AssertionError("type definition outside the module top level")


def func(d: ast.stmt) -> Any:
    assert isinstance(d, ast.FunctionDef)  # mutual def regions hold only def statements
    return at(
        d,
        Syntax.Def(
            d.name,
            type_params(d),
            [(a.arg, annotation(a.annotation)) for a in d.args.args],
            annotation(d.returns),
            seq(d.body),
        ),
    )


def type_params(node: ast.FunctionDef | ast.ClassDef | ast.TypeAlias) -> list[Any]:
    return [alpha for alpha in type_param_names(node)]


def type_def(chi: ast.stmt) -> Any:
    return at(chi, type_def_node(chi))


def type_def_node(chi: ast.stmt) -> Any:
    match chi:
        case ast.ClassDef(name=c, bases=bases):
            fields = [(x, ty_expr(psi)) for x, psi in own_fields(chi)]
            return Syntax.Dataclass(c, type_params(chi), extends(bases), fields)
        case ast.TypeAlias(name=ast.Name(id=x), value=psi):
            return Syntax.TypeStmt(x, type_params(chi), annotation(psi))
        case _:
            raise AssertionError(f"unexpected type definition: {type(chi).__name__}")


def extends(bases: list[ast.expr]) -> Any:
    match bases:
        case []:
            return Option.None_()
        case [b]:
            psi = type_expr(b)
            assert isinstance(psi, TypeName)  # other base classes rejected by the parser
            return Option.Some((name(psi.q), [ty_expr(a) for a in psi.args]))
        case _:
            raise AssertionError("multiple inheritance")


def top_stmt(body: list[ast.stmt]) -> Any:
    *items, item = statements(body)
    return reduce(
        lambda s, item_: Syntax.TopSeq(top_item(item_), s), reversed(items), top_item(item)
    )


def top_item(item: Statement) -> Any:
    match item:
        case [ast.ClassDef() | ast.TypeAlias(), *_]:
            return Syntax.TypeDefs([type_def(chi) for chi in item])
        case _:
            return Syntax.Stmt(item_stmt(item))


def import_(iota: ast.stmt) -> Any:
    return at(iota, import_node(iota))


def import_node(iota: ast.stmt) -> Any:
    match iota:
        case ast.Import(names=[alias]):
            return Syntax.Import(name(parse_name(alias.name)))
        case ast.ImportFrom(module=str(q), names=aliases):
            return Syntax.FromImport(name(parse_name(q)), [a.name for a in aliases])
        case _:
            raise AssertionError(f"unexpected import: {type(iota).__name__}")


NAME = "__name__"


def name_declaration(q: Name) -> ast.AnnAssign:
    return ast.AnnAssign(
        target=ast.Name(id=NAME, ctx=ast.Store()),
        annotation=ast.Name(id="str", ctx=ast.Load()),
        value=ast.Constant(value=str(q)),
        simple=1,
        lineno=1,
        col_offset=0,
    )


def module_body(q: Name, m: ast.Module) -> Any:
    iotas, stmts = split_imports(m.body)
    imports = [import_(iota) for iota in iotas]
    return Syntax.ModuleBody(
        imports, top_stmt([ast.fix_missing_locations(name_declaration(q)), *stmts])
    )

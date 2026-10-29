"""Messages for the reasons of the generated type checker, with its types, expressions and patterns
rendered as Python source"""

import ast
from functools import reduce
from typing import Any

from .generated import Option, Reasons, Syntax
from .syntax import BOP, PRIM_TY, UOP, node
from .type_syntax import Name


def from_name(q: Any) -> Name:
    x, xs = q
    return Name((x, *xs))


def lit_value(ell: Any) -> bool | int | float | str | None:
    match ell:
        case Syntax.LitInt(v) | Syntax.LitBool(v) | Syntax.LitFloat(v) | Syntax.LitString(v):
            assert isinstance(v, bool | int | float | str)
            return v
        case Syntax.LitNone():
            return None
        case _:
            raise AssertionError(f"unexpected literal: {ell}")


PRIMITIVE = {c: nu.value for nu, c in PRIM_TY.items()}


def render(tau: Any) -> str:
    match tau:
        case Syntax.TyPrim(nu):
            return PRIMITIVE[type(nu)]
        case Syntax.TyList(sigma):
            return f"list[{render(sigma)}]"
        case Syntax.TyTuple(taus):
            return f"tuple[{', '.join(render(c) for c in taus)}]"
        case Syntax.TyDict(sigma):
            return f"dict[str, {render(sigma)}]"
        case Syntax.TyCallable(sigmas, tau_):
            params = ", ".join(render(p) for p in sigmas)
            return f"Callable[[{params}], {render(tau_)}]"
        case Syntax.TyLiteral(ell):
            return f"Literal[{lit_value(ell)!r}]"
        case Syntax.TyVar(alpha):
            return str(alpha)
        case Syntax.TyClass(c, taus):
            args = ", ".join(render(a) for a in taus)
            return str(from_name(c)) if len(taus) == 0 else f"{from_name(c)}[{args}]"
        case Syntax.TyUnion(sigma, tau_):
            return f"{render(sigma)} | {render(tau_)}"
        case _:
            raise AssertionError(f"unexpected type: {tau}")


BOP_AST = {bop: op for op, bop in BOP.items()}
UOP_AST = {uop: op for op, uop in UOP.items()}


def render_expr(e: Any) -> str:
    return ast.unparse(from_expr(e))


def from_expr(e: Any) -> ast.expr:
    """Syntax tree of e, so that a message can quote e by unparsing it"""
    return from_expr_node(node(e))


def from_expr_node(e: Any) -> ast.expr:
    match e:
        case Syntax.ExprVar(x):
            return ast.Name(x)
        case Syntax.ExprLiteral(ell):
            return ast.Constant(lit_value(ell))
        case Syntax.ExprCall(f, (es, kws)):
            return ast.Call(
                from_expr(f),
                [from_expr(e_) for e_ in es],
                [ast.keyword(x, from_expr(e_)) for x, e_ in kws],
            )
        case Syntax.ExprDict(kvs):
            return ast.Dict([from_expr(k) for k, _ in kvs], [from_expr(v) for _, v in kvs])
        case Syntax.ExprAttribute(e_, x):
            return ast.Attribute(from_expr(e_), x)
        case Syntax.ExprSubscript(e_, e__):
            return ast.Subscript(from_expr(e_), from_expr(e__))
        case Syntax.ExprBinOp(op, e_, e__):
            op_ = BOP_AST[type(op)]
            if issubclass(op_, ast.cmpop):
                return ast.Compare(from_expr(e_), [op_()], [from_expr(e__)])
            return ast.BinOp(from_expr(e_), op_(), from_expr(e__))
        case Syntax.ExprUnOp(op, e_):
            return ast.UnaryOp(UOP_AST[type(op)](), from_expr(e_))
        case Syntax.ExprAnd(e_, e__):
            return ast.BoolOp(ast.And(), [from_expr(e_), from_expr(e__)])
        case Syntax.ExprOr(e_, e__):
            return ast.BoolOp(ast.Or(), [from_expr(e_), from_expr(e__)])
        case Syntax.ExprCond(e_, e__, e___):
            return ast.IfExp(from_expr(e__), from_expr(e_), from_expr(e___))
        case Syntax.ExprList(es):
            return ast.List([from_expr(e_) for e_ in es])
        case Syntax.ExprTuple(es):
            return ast.Tuple([from_expr(e_) for e_ in es])
        case Syntax.ExprListComp(e_, qs):
            return ast.ListComp(from_expr(e_), from_qualifiers(qs))
        case Syntax.ExprDictComp(e_, e__, qs):
            return ast.DictComp(from_expr(e_), from_expr(e__), from_qualifiers(qs))
        case Syntax.ExprLambda(xs, e_):
            args = ast.arguments(
                posonlyargs=[],
                args=[ast.arg(x) for x in xs],
                kwonlyargs=[],
                kw_defaults=[],
                defaults=[],
            )
            return ast.Lambda(args, from_expr(e_))
        case _:
            raise AssertionError(f"unexpected expression: {e}")


def from_qualifiers(qs: list[Any]) -> list[ast.comprehension]:
    """Comprehension nodes of the qualifiers qs, one per generator, holding the guards that follow that
    generator"""

    def add(gs: list[ast.comprehension], q: Any) -> list[ast.comprehension]:
        match node(q):
            case Syntax.Generator(x, e):
                return [*gs, ast.comprehension(ast.Name(x), from_expr(e), [], 0)]
            case Syntax.Guard(e):
                *gs_, g = gs
                return [*gs_, ast.comprehension(g.target, g.iter, [*g.ifs, from_expr(e)], 0)]
            case _:
                raise AssertionError(f"unexpected qualifier: {q}")

    return reduce(add, qs, [])


BINARY = {
    Syntax.BOpBitOr: "|",
    Syntax.BOpEq: "==",
    Syntax.BOpNeq: "!=",
    Syntax.BOpLt: "<",
    Syntax.BOpLeq: "<=",
    Syntax.BOpGt: ">",
    Syntax.BOpGeq: ">=",
    Syntax.BOpAdd: "+",
    Syntax.BOpSub: "-",
    Syntax.BOpMul: "*",
    Syntax.BOpDiv: "/",
    Syntax.BOpFloorDiv: "//",
    Syntax.BOpMod: "%",
    Syntax.BOpPow: "**",
    Syntax.BOpIn: "in",
    Syntax.BOpNotIn: "not in",
}
UNARY = {Syntax.UOpNot: "not", Syntax.UOpPos: "+", Syntax.UOpNeg: "-"}

SEQUENCE_KIND = {
    Syntax.TupleKind(): "tuple",
    Syntax.ListKind(): "list",
    Syntax.RangeKind(): "range",
}


def render_pat(p: Any) -> str:
    return render_pat_node(node(p))


def render_pat_node(p: Any) -> str:
    match p:
        case Syntax.PatLiteral(ell):
            return ast.unparse(ast.Constant(lit_value(ell)))
        case Syntax.PatVar(x):
            return str(x)
        case Syntax.PatWildcard():
            return "_"
        case Syntax.PatAs(p_, x):
            return f"{render_pat(p_)} as {x}"
        case Syntax.PatList(ps):
            return "[" + ", ".join(map(render_pat, ps)) + "]"
        case Syntax.PatTuple(ps):
            return "(" + ", ".join(map(render_pat, ps)) + ")"
        case Syntax.PatDict(kps):
            items = (f"{ast.unparse(ast.Constant(w))}: {render_pat(q)}" for w, q in kps)
            return "{" + ", ".join(items) + "}"
        case Syntax.PatConstr(q, (ps, kps)):
            args = [render_pat(p_) for p_ in ps] + [f"{x}={render_pat(p_)}" for x, p_ in kps]
            return f"{from_name(q)}({', '.join(args)})"
        case _:
            raise AssertionError(f"unexpected pattern: {p}")


def message(r: Any) -> str:
    match r:
        case Reasons.DuplicateField(x, c):
            return f"duplicate field '{x}' in class '{c}'"
        case Reasons.InheritedField(x, c, d):
            return f"field '{x}' of class '{c}' is also a field of base class '{d}'"
        case Reasons.UndefinedVariable(x):
            return f"'{x}' is not defined"
        case Reasons.UnassignedVariable(x):
            return f"'{x}' is declared but not yet assigned"
        case Reasons.PossiblyUnassigned(x, declared_in_branch):
            qualifier = ": declared in a branch" if declared_in_branch else ""
            return f"'{x}' is not definitely assigned{qualifier}"
        case Reasons.UnboundName(x):
            return f"'{x}' is unbound"
        case Reasons.Redeclaration(x):
            return f"'{x}' is already declared"
        case Reasons.UndeclaredAssignment(x):
            return f"'{x}' is assigned but never declared"
        case Reasons.AssignmentBeforeDeclaration(x):
            return f"'{x}' is assigned before its declaration"
        case Reasons.Reassignment(x):
            return f"'{x}' is already assigned"
        case Reasons.PossibleReassignment(x):
            return f"'{x}' may already be assigned"
        case Reasons.CapturedGeneratorVariable(x):
            return f"'{x}' bound by generator, captured by lambda"
        case Reasons.UnreachableStatement():
            return "unreachable statement"
        case Reasons.ConstructorArityMismatch(c, m, n):
            return f"constructor for '{c}' expects {m} arguments, got {n}"
        case Reasons.UnknownConstructorKeyword(c, xs):
            return f"constructor keywords for '{c}' must be {', '.join(xs)}"
        case Reasons.PatternArityMismatch(c, m, n):
            return f"pattern for '{c}' expects {m} sub-patterns, got {n}"
        case Reasons.UnknownFieldInPattern(c, xs):
            return f"pattern keywords for '{c}' must be {', '.join(xs)}"
        case Reasons.RangePattern():
            return "'range' not permitted in a constructor pattern"
        case Reasons.PatternClassUndetermined(c, tau):
            return f"type arguments of '{c}' in pattern not determined by type {render(tau)}"
        case Reasons.SequenceKindMismatch(kind, tau, other):
            return f"{SEQUENCE_KIND[kind]} pattern at {render(tau)}, which has {SEQUENCE_KIND[other]} values"
        case Reasons.UnreachableCase(p):
            return f"case {render_pat(p)} is unreachable"
        case Reasons.MissingReturnMatchPartial(tau):
            return (
                f"cases leave remaining type {render(tau)}, so the function does not always return"
            )
        case Reasons.MissingReturnAssertion():
            return (
                "assertion of expression of type Literal[False] other than False, "
                "so the function does not always return"
            )
        case Reasons.NotPredefinedName(x):
            return f"'{x}' is not bound as a predefined name"
        case Reasons.NotTypeExpression(e):
            return f"'{render_expr(e)}' is not a type expression"
        case Reasons.NotClass(q):
            return f"'{from_name(q)}' is not a declared class"
        case Reasons.ClassArityMismatch(q, m, n):
            return f"class '{from_name(q)}' expects {m} type arguments, given {n}"
        case Reasons.TypeAliasArityMismatch(q, m, n):
            return f"type alias '{from_name(q)}' expects {m} type arguments, given {n}"
        case Reasons.CyclicTypeAlias(x):
            return f"type alias '{x}' is cyclic"
        case Reasons.DuplicateMember(x, q):
            return (
                f"duplicate member of module '{from_name(q)}': "
                f"it defines '{x}' and also has submodule '{from_name(q)}.{x}'"
            )
        case Reasons.SubmoduleNotImported(q):
            return f"submodule '{from_name(q)}' is not imported"
        case Reasons.UnassignedMember(x, q):
            return f"member '{x}' of module '{from_name(q)}' is not definitely assigned"
        case Reasons.TopLevelAssertFalse():
            return "module body definitely reaches 'assert False'"
        case Reasons.UnknownModule(q):
            return f"unknown module '{from_name(q)}'"
        case Reasons.DuplicateImportedName(x):
            return f"name '{x}' imported twice"
        case Reasons.UnknownMember(x, q):
            return f"module '{from_name(q)}' has no member '{x}'"
        case Reasons.ModuleAsValue(q):
            return f"'{from_name(q)}' refers to a module; modules are not first-class values"
        case Reasons.ImportOfContainedModule(q, q_):
            return (
                f"'{from_name(q)}' is contained in importing module '{from_name(q_)}'; "
                f"plain import not allowed, write 'from {from_name(q)} import <name>'"
            )
        case Reasons.PredefinedNameAsValue(q):
            return f"'{from_name(q)}' is usable only in annotations or as a decorator"
        case Reasons.TypeParameterAsValue(x):
            return f"'{x}' is a type parameter, usable only in annotations"
        case Reasons.TypeSchemeAsValue(q):
            return f"type arguments of '{from_name(q)}' cannot be inferred"
        case Reasons.NoTypeArgument(alpha):
            return f"type parameter '{alpha}' has no type argument"
        case Reasons.ClassAsValue(q):
            return f"'{from_name(q)}' refers to a class; classes are not first-class values"
        case Reasons.TypeAliasAsValue(q):
            return f"'{from_name(q)}' is a type alias, usable only in annotations"
        case Reasons.NoBinaryOverload(op, sigma, sigma_):
            return (
                f"no overload of '{BINARY[type(op)]}' at operand types "
                f"{render(sigma)} and {render(sigma_)}"
            )
        case Reasons.NoUnaryOverload(op, sigma):
            return f"no overload of '{UNARY[type(op)]}' at operand type {render(sigma)}"
        case Reasons.NotCallable(tau):
            return f"values of type {render(tau)} cannot be called"
        case Reasons.KeywordArgumentsNotConstructor():
            return "keyword arguments in a call other than a constructor call"
        case Reasons.CallArityMismatch(m, n):
            return f"call expects {m} arguments, given {n}"
        case Reasons.NoneResult():
            return "call returning None used as an expression"
        case Reasons.TypeMismatch(tau, sigma):
            return f"expected type {render(tau)}, given {render(sigma)}"
        case Reasons.LambdaTypeMismatch(tau, Option.Some(n)):
            return f"expected type {render(tau)}, given a lambda of {n} parameter{'' if n == 1 else 's'}"
        case Reasons.LambdaTypeMismatch(tau, Option.None_()):
            return f"expected type {render(tau)}, given a lambda"
        case Reasons.NotSubscriptable(tau):
            return f"values of type {render(tau)} cannot be subscripted"
        case Reasons.TupleIndexOutOfRange(i, n):
            return f"index {i} out of range for tuple of length {n}"
        case Reasons.NotIterable(tau):
            return f"values of type {render(tau)} cannot be iterated"
        case Reasons.NotSynthesised():
            return "cannot infer type of this expression"
        case Reasons.UnknownField(c, x):
            return f"class '{c}' has no field '{x}'"
        case Reasons.NoAttributes(tau):
            return f"values of type {render(tau)} have no attributes"
        case Reasons.BareReturn(tau):
            return f"bare return in function with result type {render(tau)}"
        case Reasons.MissingReturn(x, tau):
            return f"'{x}' declares result type {render(tau)} but does not always return"
        case Reasons.MypyCompatibility(r_):
            return f"{message(r_)} (mypy compatibility)"
        case Reasons.Located(_, r_):
            return message(r_)
        case Reasons.ImportCycle(qs):
            return f"import cycle: {' -> '.join(str(from_name(q)) for q in qs)}"
        case _:
            raise AssertionError(f"unexpected reason: {r}")

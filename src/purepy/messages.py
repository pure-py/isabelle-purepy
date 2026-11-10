"""Messages for the reasons of the generated type checker, with names, types, expressions and patterns
unparsed to Python source, and values in the representation given by Python"""

import ast
import builtins
import importlib
import sys
from functools import reduce

from purepy_conformance import Classification, excluded

from .generated import Option, Reasons, Syntax, Values
from .syntax import (
    BOP_AST,
    PRIMITIVE,
    SYMBOL,
    UOP_AST,
    Expr,
    Lit,
    Pat,
    Qualifier,
    Reason,
    Ty,
    Val,
    node,
    unparse_name,
)

BY_DESIGN = Classification.BY_DESIGN
FOR_NOW = Classification.FOR_NOW
BUILTINS = set(dir(builtins))
PREDEFINED_MODULES = {"sys", "typing", "dataclasses"}
# Built-ins, module members and type attributes excluded by design, by qualified name
EXCLUDED_BY_DESIGN = {
    "setattr",
    "delattr",
    "id",
    "iter",
    "next",
    "eval",
    "exec",
    "getattr",
    "globals",
    "locals",
    "vars",
    "__import__",
    "typing.Any",
    "typing.cast",
    "list.append",
    "list.extend",
    "list.insert",
    "list.remove",
    "list.pop",
    "list.clear",
    "list.sort",
    "list.reverse",
    "dict.update",
    "dict.pop",
    "dict.popitem",
    "dict.clear",
    "dict.setdefault",
}


def lit_value(ell: Lit) -> bool | int | float | str | None:
    match ell:
        case Syntax.LitInt(v) | Syntax.LitBool(v) | Syntax.LitFloat(v) | Syntax.LitString(v):
            assert isinstance(v, bool | int | float | str)
            return v
        case Syntax.LitNone():
            return None
        case _:
            raise AssertionError(f"unexpected literal: {ell}")


def unparse_type(tau: Ty) -> str:
    match tau:
        case Syntax.TyPrim(nu):
            return PRIMITIVE[type(nu)]
        case Syntax.TyList(sigma):
            return f"list[{unparse_type(sigma)}]"
        case Syntax.TyTuple(taus):
            return f"tuple[{', '.join(unparse_type(c) for c in taus)}]"
        case Syntax.TyDict(sigma):
            return f"dict[str, {unparse_type(sigma)}]"
        case Syntax.TyCallable(sigmas, tau_):
            params = ", ".join(unparse_type(p) for p in sigmas)
            return f"Callable[[{params}], {unparse_type(tau_)}]"
        case Syntax.TyLiteral(ell):
            return f"Literal[{lit_value(ell)!r}]"
        case Syntax.TyVar(alpha):
            return str(alpha)
        case Syntax.TyClass(c, taus):
            args = ", ".join(unparse_type(a) for a in taus)
            return unparse_name(c) if len(taus) == 0 else f"{unparse_name(c)}[{args}]"
        case Syntax.TyUnion(sigma, tau_):
            return f"{unparse_type(sigma)} | {unparse_type(tau_)}"
        case _:
            raise AssertionError(f"unexpected type: {tau}")


def unparse_expr(e: Expr) -> str:
    def ast_expr(e: Expr) -> ast.expr:
        match node(e):
            case Syntax.ExprVar(x):
                return ast.Name(x)
            case Syntax.ExprLiteral(ell):
                return ast.Constant(lit_value(ell))
            case Syntax.ExprCall(f, (es, kws)):
                return ast.Call(
                    ast_expr(f),
                    [ast_expr(e_) for e_ in es],
                    [ast.keyword(x, ast_expr(e_)) for x, e_ in kws],
                )
            case Syntax.ExprDict(kvs):
                return ast.Dict([ast_expr(k) for k, _ in kvs], [ast_expr(v) for _, v in kvs])
            case Syntax.ExprAttribute(e_, x):
                return ast.Attribute(ast_expr(e_), x)
            case Syntax.ExprSubscript(e_, e__):
                return ast.Subscript(ast_expr(e_), ast_expr(e__))
            case Syntax.ExprBinOp(op, e_, e__):
                op_ = BOP_AST[type(op)]
                if issubclass(op_, ast.cmpop):
                    return ast.Compare(ast_expr(e_), [op_()], [ast_expr(e__)])
                return ast.BinOp(ast_expr(e_), op_(), ast_expr(e__))
            case Syntax.ExprUnOp(op, e_):
                return ast.UnaryOp(UOP_AST[type(op)](), ast_expr(e_))
            case Syntax.ExprAnd(e_, e__):
                return ast.BoolOp(ast.And(), [ast_expr(e_), ast_expr(e__)])
            case Syntax.ExprOr(e_, e__):
                return ast.BoolOp(ast.Or(), [ast_expr(e_), ast_expr(e__)])
            case Syntax.ExprCond(e_, e__, e___):
                return ast.IfExp(ast_expr(e__), ast_expr(e_), ast_expr(e___))
            case Syntax.ExprList(es):
                return ast.List([ast_expr(e_) for e_ in es])
            case Syntax.ExprTuple(es):
                return ast.Tuple([ast_expr(e_) for e_ in es])
            case Syntax.ExprListComp(e_, qs):
                return ast.ListComp(ast_expr(e_), ast_comprehensions(qs))
            case Syntax.ExprDictComp(e_, e__, qs):
                return ast.DictComp(ast_expr(e_), ast_expr(e__), ast_comprehensions(qs))
            case Syntax.ExprLambda(xs, e_):
                args = ast.arguments(
                    posonlyargs=[],
                    args=[ast.arg(x) for x in xs],
                    kwonlyargs=[],
                    kw_defaults=[],
                    defaults=[],
                )
                return ast.Lambda(args, ast_expr(e_))
            case _:
                raise AssertionError(f"unexpected expression: {e}")

    def ast_comprehensions(qs: list[Qualifier]) -> list[ast.comprehension]:
        """Comprehension node per generator in qs, whose conditions are the guards following the generator"""

        def add(gs: list[ast.comprehension], q: Qualifier) -> list[ast.comprehension]:
            match node(q):
                case Syntax.Generator(x, e):
                    return [*gs, ast.comprehension(ast.Name(x), ast_expr(e), [], 0)]
                case Syntax.Guard(e):
                    *gs_, g = gs
                    return [*gs_, ast.comprehension(g.target, g.iter, [*g.ifs, ast_expr(e)], 0)]
                case _:
                    raise AssertionError(f"unexpected qualifier: {q}")

        return reduce(add, qs, [])

    return ast.unparse(ast_expr(e))


SEQUENCE_KIND = {
    Syntax.TupleKind(): "tuple",
    Syntax.ListKind(): "list",
    Syntax.RangeKind(): "range",
}


def unparse_pat(p: Pat) -> str:
    match node(p):
        case Syntax.PatLiteral(ell):
            return ast.unparse(ast.Constant(lit_value(ell)))
        case Syntax.PatVar(x):
            return str(x)
        case Syntax.PatWildcard():
            return "_"
        case Syntax.PatAs(p_, x):
            return f"{unparse_pat(p_)} as {x}"
        case Syntax.PatList(ps):
            return "[" + ", ".join(map(unparse_pat, ps)) + "]"
        case Syntax.PatTuple(ps):
            return "(" + ", ".join(map(unparse_pat, ps)) + ")"
        case Syntax.PatDict(kps):
            items = (f"{ast.unparse(ast.Constant(w))}: {unparse_pat(q)}" for w, q in kps)
            return "{" + ", ".join(items) + "}"
        case Syntax.PatConstr(q, (ps, kps)):
            args = [unparse_pat(p_) for p_ in ps] + [f"{x}={unparse_pat(p_)}" for x, p_ in kps]
            return f"{unparse_name(q)}({', '.join(args)})"
        case _:
            raise AssertionError(f"unexpected pattern: {p}")


def unparse_value(v: Val) -> str:
    """Representation of v given by Python"""
    match v:
        case Values.VLit(ell):
            return repr(lit_value(ell))
        case Values.VList(us):
            return "[" + ", ".join(map(unparse_value, us)) + "]"
        case Values.VTuple(us):
            return "(" + ", ".join(map(unparse_value, us)) + ("," if len(us) == 1 else "") + ")"
        case Values.VDict(wus):
            return "{" + ", ".join(f"{w!r}: {unparse_value(u)}" for w, u in wus) + "}"
        case Values.VObject(c, fields):
            x = Syntax.variables(c)[-1]
            return f"{x}(" + ", ".join(f"{y}={unparse_value(u)}" for y, u in fields) + ")"
        case Values.VClass(c):
            return f"<class '{unparse_name(c)}'>"
        case Values.VPrim(f):
            return f"<built-in function {type(f).__name__.removeprefix('Prim').lower()}>"
        case Values.VModStub(q) | Values.VModLoaded(q, _):
            return f"<module '{unparse_name(q)}'>"
        case _:
            return f"<{type(v).__name__.rstrip('_')}>"


def builtin_type(tau: Ty) -> type | None:
    """Python class of the values of a built-in type; None for other types"""
    match tau:
        case Syntax.TyList(_):
            return list
        case Syntax.TyDict(_):
            return dict
        case Syntax.TyTuple(_):
            return tuple
        case Syntax.TyPrim(nu):
            return {"bool": bool, "int": int, "float": float, "str": str}.get(PRIMITIVE[type(nu)])
        case Syntax.TyLiteral(ell):
            return type(lit_value(ell))
        case _:
            return None


def callee_name(e: Expr) -> str | None:
    """Callee as a dotted name; None for any other expression"""
    match node(e):
        case Syntax.ExprVar(x):
            return str(x)
        case Syntax.ExprAttribute(e_, x):
            q = callee_name(e_)
            return None if q is None else f"{q}.{x}"
        case _:
            return None


def builtin_class(x: str) -> bool:
    return isinstance(getattr(builtins, x, None), type)


def excluded_name(name: str) -> tuple[str, Classification]:
    """Qualified name of an excluded built-in, module member or type attribute, with its classification"""
    return (f"'{name}'", BY_DESIGN if name in EXCLUDED_BY_DESIGN else FOR_NOW)


def unwrapped(r: Reason) -> Reason:
    """r without the rule it violates or the judgement which selects no rule"""
    match r:
        case Reasons.Violates(_, r_) | Reasons.SelectsNoRule(_, r_):
            return unwrapped(r_)
        case Reasons.Located(p, r_):
            return Reasons.Located(p, unwrapped(r_))
        case Reasons.MypyCompatibility(r_):
            return Reasons.MypyCompatibility(unwrapped(r_))
        case _:
            return r


def position(r: Reason) -> tuple[int, int] | None:
    match unwrapped(r):
        case Reasons.Located((line, col), _):
            return (line, col)
        case _:
            return None


def excluded_feature(r: Reason) -> tuple[str, Classification] | None:
    """Excluded Python feature rejected by r, with its classification; None if r rejects a use of an included
    feature"""
    match unwrapped(r):
        case Reasons.Located(_, r_):
            return excluded_feature(r_)
        case Reasons.PrintInFunction():
            return ("print inside function", FOR_NOW)
        case Reasons.UndefinedVariable(x) if x in BUILTINS:
            return excluded_name(x)
        case Reasons.PredefinedNameAsPattern(q) if builtin_class(unparse_name(q)):
            return (f"constructor pattern for built-in class '{unparse_name(q)}'", FOR_NOW)
        case Reasons.UnknownModule(q) if Syntax.root(q) in sys.stdlib_module_names:
            return (f"module '{unparse_name(q)}'", FOR_NOW)
        case Reasons.UnknownMember(x, q) if (
            m := unparse_name(q)
        ) in PREDEFINED_MODULES and hasattr(importlib.import_module(m), x):
            return excluded_name(f"{m}.{x}")
        case Reasons.NoAttributes(tau, x) if (t := builtin_type(tau)) is not None and hasattr(t, x):
            return excluded_name(f"{t.__name__}.{x}")
        case Reasons.CallArityMismatch(e, 1, 2) if callee_name(e) == "round":
            return ("round with second argument", FOR_NOW)
        case Reasons.CallArityMismatch(e, 1, 0) if callee_name(e) in ("sys.exit", "exit"):
            return ("sys.exit with no arguments", FOR_NOW)
        case _:
            return None


def classification(r: Reason) -> Classification | None:
    feature = excluded_feature(r)
    return None if feature is None else feature[1]


def message(r: Reason) -> str:
    feature = excluded_feature(r)
    if feature is not None:
        return str(excluded(*feature))
    match unwrapped(r):
        case Reasons.DuplicateField(x, c):
            return f"duplicate field '{x}' in class '{c}'"
        case Reasons.DuplicateTypeParameter(a, c):
            return f"duplicate type parameter '{a}' in class '{c}'"
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
        case Reasons.PatternBindsTwice(x):
            return f"pattern binds '{x}' twice"
        case Reasons.RangePattern():
            return "'range' not permitted in a constructor pattern"
        case Reasons.RangeBase():
            return "'range' not permitted as a base class"
        case Reasons.PatternClassUndetermined(c, tau):
            return f"type arguments of '{c}' in pattern not determined by type {unparse_type(tau)}"
        case Reasons.SequenceKindMismatch(kind, tau, other):
            return f"{SEQUENCE_KIND[kind]} pattern at {unparse_type(tau)}, which has {SEQUENCE_KIND[other]} values"
        case Reasons.IntLiteralFloatValues(tau):
            return f"int literal pattern at {unparse_type(tau)}, which has float values"
        case Reasons.DictPatternDictValues(tau):
            return f"dictionary pattern at {unparse_type(tau)}, which has dictionary values"
        case Reasons.UnreachableCase(p):
            return f"case {unparse_pat(p)} is unreachable"
        case Reasons.MissingReturnMatchPartial(tau):
            return f"cases leave remaining type {unparse_type(tau)}, so the function does not always return"
        case Reasons.MissingReturnAssertion():
            return (
                "assertion of expression of type Literal[False] other than False, "
                "so the function does not always return"
            )
        case Reasons.NotPredefinedName(x):
            return f"'{x}' is not bound as a predefined name"
        case Reasons.NotTypeExpression(e):
            return f"'{unparse_expr(e)}' is not a type expression"
        case Reasons.NotClass(q) | Reasons.PredefinedNameAsPattern(q):
            return f"'{unparse_name(q)}' is not a declared class"
        case Reasons.ClassArityMismatch(q, m, n):
            return f"class '{unparse_name(q)}' expects {m} type arguments, given {n}"
        case Reasons.TypeAliasArityMismatch(q, m, n):
            return f"type alias '{unparse_name(q)}' expects {m} type arguments, given {n}"
        case Reasons.CyclicTypeAlias(x):
            return f"type alias '{x}' is cyclic"
        case Reasons.DuplicateMember(x, q):
            return (
                f"duplicate member of module '{unparse_name(q)}': "
                f"it defines '{x}' and also has submodule '{unparse_name(q)}.{x}'"
            )
        case Reasons.SubmoduleNotImported(q):
            return f"submodule '{unparse_name(q)}' is not imported"
        case Reasons.UnassignedMember(x, q):
            return f"member '{x}' of module '{unparse_name(q)}' is not definitely assigned"
        case Reasons.TopLevelAssertFalse():
            return "module body definitely reaches 'assert False'"
        case Reasons.UnknownModule(q):
            return f"unknown module '{unparse_name(q)}'"
        case Reasons.DuplicateImportedName(x):
            return f"name '{x}' imported twice"
        case Reasons.UnknownMember(x, q):
            return f"module '{unparse_name(q)}' has no member '{x}'"
        case Reasons.ModuleAsValue(q):
            return f"'{unparse_name(q)}' refers to a module; modules are not first-class values"
        case Reasons.ImportOfContainedModule(q, q_):
            return (
                f"'{unparse_name(q)}' is contained in importing module '{unparse_name(q_)}'; "
                f"plain import not allowed, write 'from {unparse_name(q)} import <name>'"
            )
        case Reasons.PredefinedNameAsValue(q):
            return f"'{unparse_name(q)}' is usable only in annotations or as a decorator"
        case Reasons.TypeParameterAsValue(x):
            return f"'{x}' is a type parameter, usable only in annotations"
        case Reasons.TypeSchemeAsValue(q):
            return f"type arguments of '{unparse_name(q)}' cannot be inferred"
        case Reasons.NoTypeArgument(alpha):
            return f"type parameter '{alpha}' has no type argument"
        case Reasons.ClassAsValue(q):
            return f"'{unparse_name(q)}' refers to a class; classes are not first-class values"
        case Reasons.TypeAliasAsValue(q):
            return f"'{unparse_name(q)}' is a type alias, usable only in annotations"
        case Reasons.NoBinaryOverload(op, sigma, sigma_):
            return (
                f"no overload of '{SYMBOL[BOP_AST[type(op)]]}' at operand types "
                f"{unparse_type(sigma)} and {unparse_type(sigma_)}"
            )
        case Reasons.NoUnaryOverload(op, sigma):
            return f"no overload of '{SYMBOL[UOP_AST[type(op)]]}' at operand type {unparse_type(sigma)}"
        case Reasons.NotCallable(tau):
            return f"values of type {unparse_type(tau)} cannot be called"
        case Reasons.KeywordArgumentsNotConstructor():
            return "keyword arguments in a call other than a constructor call"
        case Reasons.CallArityMismatch(_, m, n):
            return f"call expects {m} arguments, given {n}"
        case Reasons.NoneResult():
            return "call returning None used as an expression"
        case Reasons.TypeMismatch(tau, sigma):
            return f"expected type {unparse_type(tau)}, given {unparse_type(sigma)}"
        case Reasons.LambdaTypeMismatch(tau, Option.Some(n)):
            return f"expected type {unparse_type(tau)}, given a lambda of {n} parameter{'' if n == 1 else 's'}"
        case Reasons.LambdaTypeMismatch(tau, Option.None_()):
            return f"expected type {unparse_type(tau)}, given a lambda"
        case Reasons.NotSubscriptable(tau):
            return f"values of type {unparse_type(tau)} cannot be subscripted"
        case Reasons.TupleIndexOutOfRange(i, n):
            return f"index {i} out of range for tuple of length {n}"
        case Reasons.NotIterable(tau):
            return f"values of type {unparse_type(tau)} cannot be iterated"
        case Reasons.NotSynthesised():
            return "cannot infer type of this expression"
        case Reasons.UnknownField(c, x):
            return f"class '{c}' has no field '{x}'"
        case Reasons.NoAttributes(tau, _):
            return f"values of type {unparse_type(tau)} have no attributes"
        case Reasons.BareReturn(tau):
            return f"bare return in function with result type {unparse_type(tau)}"
        case Reasons.MissingReturn(x, tau):
            return f"'{x}' declares result type {unparse_type(tau)} but does not always return"
        case Reasons.ReturnOutsideFunction():
            return "'return' outside function"
        case Reasons.MypyCompatibility(r_):
            return f"{message(r_)} (mypy compatibility)"
        case Reasons.Located(_, r_):
            return message(r_)
        case Reasons.ImportCycle(qs):
            return f"import cycle: {' -> '.join(unparse_name(q) for q in qs)}"
        case _:
            raise AssertionError(f"unexpected reason: {r}")

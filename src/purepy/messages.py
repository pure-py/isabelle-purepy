"""Messages for the reasons of the generated type checker, with names, types, expressions and patterns
unparsed to Python source, and values in the representation given by Python"""

import builtins
import importlib
import sys

from purepy_conformance import Classification, excluded

from .generated import Option, Reasons, Syntax
from .syntax import (
    BOP_AST,
    PRIMITIVE,
    SYMBOL,
    UOP_AST,
    Expr,
    Reason,
    Ty,
    lit_value,
    node,
    unparse_expr,
    unparse_name,
    unparse_pat,
    unparse_type,
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


SEQUENCE_KIND = {
    Syntax.TupleKind(): "tuple",
    Syntax.ListKind(): "list",
    Syntax.RangeKind(): "range",
}


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

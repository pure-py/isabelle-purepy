import ast
from collections.abc import Callable, Sequence
from functools import reduce
from itertools import takewhile
from typing import Any

from .generated import Option, Positions, Syntax

# Sorts of the mechanisation, Any until the generator annotates them: #7, Type annotations in generated code,
# https://github.com/pure-py/isabelle-python-codegen/issues/7
type Var = str
type QualifiedName = Any
type Lit = Any
type Pat = Any
type Expr = Any
type Qualifier = Any
type TyExpr = Any
type Ty = Any
type Import = Any
type Stmt = Any
type Func = Any
type TypeDef = Any
type TopStmt = Any
type ModuleBody = Any
type Program = Any
type Reason = Any
# Name as a tuple of variables, hashable unlike the generated form; delete with #24, Names as a datatype,
# https://github.com/pure-py/isabelle-purepy/issues/24
type Name = tuple[Var, ...]


def parse_name(name: str) -> Name:
    return tuple(name.split("."))


type Statement = ast.stmt | list[ast.FunctionDef] | list[ast.ClassDef | ast.TypeAlias]


def is_import(s: ast.stmt) -> bool:
    return isinstance(s, (ast.Import, ast.ImportFrom))


def split_imports(body: list[ast.stmt]) -> tuple[list[ast.stmt], list[ast.stmt]]:
    iotas = list(takewhile(is_import, body))
    return iotas, body[len(iotas) :]


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


def extend_type_region(
    region: list[ast.ClassDef | ast.TypeAlias], rest: list[ast.stmt]
) -> list[Statement]:
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


def type_param_names(node: ast.FunctionDef | ast.ClassDef | ast.TypeAlias) -> tuple[Var, ...]:
    alphas = tuple(p.name for p in node.type_params if isinstance(p, ast.TypeVar))
    assert len(alphas) == len(node.type_params)
    return alphas


OP_SYMBOLS: dict[type, str] = {
    ast.BitOr: "|",
    ast.Eq: "==",
    ast.NotEq: "!=",
    ast.Lt: "<",
    ast.LtE: "<=",
    ast.Gt: ">",
    ast.GtE: ">=",
    ast.Add: "+",
    ast.Sub: "-",
    ast.Mult: "*",
    ast.Div: "/",
    ast.FloorDiv: "//",
    ast.Mod: "%",
    ast.Pow: "**",
    ast.In: "in",
    ast.NotIn: "not in",
    ast.Not: "not",
    ast.UAdd: "+",
    ast.USub: "-",
    ast.BitAnd: "&",
    ast.BitXor: "^",
    ast.LShift: "<<",
    ast.RShift: ">>",
    ast.MatMult: "@",
    ast.Invert: "~",
}


class Unsupported(Exception):
    exit_code: int  # overridden by subclass
    msg: str
    module: Name | None = None

    def __init__(self, node: ast.AST, msg: str):
        self.line: int | None = getattr(node, "lineno", None)
        self.col: int | None = getattr(node, "col_offset", None)
        self.msg = msg
        super().__init__(msg)


def not_allowed(construct: str) -> str:
    return f"{construct} not allowed in PurePy"


class NotAllowed(Unsupported):
    exit_code = 1

    def __init__(self, node: ast.AST, construct: str):
        super().__init__(node, not_allowed(construct))


class ParseError(Unsupported):
    exit_code = 1

    def __init__(self, e: SyntaxError):
        self.line = e.lineno
        self.col = None if e.offset is None else e.offset - 1
        self.end_line = e.end_lineno
        self.end_col = None if e.end_offset is None else e.end_offset - 1
        self.msg = f"parse error: {e.msg}"
        Exception.__init__(self, self.msg)


class PatList(ast.MatchSequence):
    pass


class PatTuple(ast.MatchSequence):
    pass


def map_tree(f: Callable[[ast.AST], ast.AST], node: ast.AST) -> ast.AST:
    """Rebuild node bottom-up, applying f to each node. Subtrees f leaves alone are shared, not copied."""
    fields: dict[str, object] = {}
    for name in node._fields:
        v = getattr(node, name)
        match v:
            case ast.AST():
                fields[name] = map_tree(f, v)
            case list():
                new = [map_tree(f, x) if isinstance(x, ast.AST) else x for x in v]
                fields[name] = v if all(a is b for a, b in zip(new, v)) else new
            case _:
                fields[name] = v
    unchanged = all(fields[name] is getattr(node, name) for name in node._fields)
    return f(node if unchanged else ast.copy_location(type(node)(**fields), node))


def fold_negative(node: ast.AST) -> ast.AST:
    """Unary minus applied to a numeric literal is a literal."""
    match node:
        case ast.UnaryOp(op=ast.USub(), operand=ast.Constant(value=n)) if isinstance(
            n, (int, float)
        ) and not isinstance(n, bool):
            return ast.copy_location(ast.Constant(value=-n), node)
        case _:
            return node


def classify_sequence(source: str) -> Callable[[ast.AST], ast.AST]:
    """AST doesn't record brackets or parentheses; classify sequence patterns by source text."""

    def classify(node: ast.AST) -> ast.AST:
        match node:
            case ast.MatchSequence(patterns=ps):
                segment = ast.get_source_segment(source, node)
                assert segment is not None
                if segment.startswith("["):
                    return ast.copy_location(PatList(patterns=ps), node)
                return ast.copy_location(PatTuple(patterns=ps), node)
            case _:
                return node

    return classify


def parse(source: str, filename: str) -> ast.Module:
    classify = classify_sequence(source)
    m = map_tree(lambda node: classify(fold_negative(node)), ast.parse(source, filename=filename))
    assert isinstance(m, ast.Module)
    return m


def check_syntax_stmt(node: ast.stmt) -> None:
    match node:
        case ast.Pass():
            pass
        case ast.Assign():
            if len(node.targets) != 1:
                raise NotAllowed(node, "multiple assignment targets")
            target = node.targets[0]
            match target:
                case ast.Subscript():
                    raise NotAllowed(node, "item assignment")
                case ast.Attribute():
                    raise NotAllowed(node, "attribute assignment")
                case ast.Name():
                    check_syntax_expr(node.value)
                case _:
                    raise NotAllowed(node, "unpacking assignment")
        case ast.Return():
            if node.value is not None:
                check_syntax_expr(node.value)
        case ast.If():
            check_syntax_expr(node.test)
            check_syntax_body(node.body)
            check_syntax_body(node.orelse)
        case ast.FunctionDef():
            check_syntax_type_params(node)
            check_syntax_arguments(node.args)
            if len(node.decorator_list) > 0:
                raise NotAllowed(node, "decorators")
            if any(a.annotation is None for a in node.args.args):
                raise NotAllowed(node, "unannotated parameter")
            if node.returns is None:
                raise NotAllowed(node, "unannotated return type")
            check_syntax_annotation(node.returns)
            check_syntax_body(node.body)
        case ast.Expr():
            check_syntax_expr(node.value)
        case ast.Assert():
            check_syntax_expr(node.test)
            if node.msg is not None:
                check_syntax_expr(node.msg)
        case ast.AugAssign():
            raise NotAllowed(node, "augmented assignment (+=, etc.)")
        case ast.AnnAssign():
            if not isinstance(node.target, ast.Name):
                raise NotAllowed(node, "assignment target other than a simple name")
            check_syntax_annotation(node.annotation)
            if node.value is not None:
                check_syntax_expr(node.value)
        case ast.Delete():
            raise NotAllowed(node, "del")
        case ast.For():
            raise NotAllowed(node, "for loops")
        case ast.While():
            raise NotAllowed(node, "while loops")
        case ast.With():
            raise NotAllowed(node, "with statements")
        case ast.AsyncFunctionDef() | ast.AsyncFor() | ast.AsyncWith():
            raise NotAllowed(node, "async")
        case ast.Raise():
            raise NotAllowed(node, "raise")
        case ast.Try() | ast.TryStar():
            raise NotAllowed(node, "try/except")
        case ast.Import() | ast.ImportFrom():
            raise NotAllowed(node, "import outside the module top level")
        case ast.Global():
            raise NotAllowed(node, "global")
        case ast.Nonlocal():
            raise NotAllowed(node, "nonlocal")
        case ast.ClassDef():
            raise NotAllowed(node, "class definition outside the module top level")
        case ast.TypeAlias():
            raise NotAllowed(node, "type statement outside the module top level")
        case ast.Match():
            check_syntax_expr(node.subject)
            for case in node.cases:
                if case.guard is not None:
                    raise NotAllowed(case, "case guards")
                check_syntax_pattern(case.pattern)
                dup = duplicate(bound(case.pattern))
                if dup is not None:
                    raise NotAllowed(case.pattern, f"duplicate variable {dup} in pattern")
                check_syntax_body(case.body)
        case ast.Break():
            raise NotAllowed(node, "break")
        case ast.Continue():
            raise NotAllowed(node, "continue")
        case _:
            raise NotAllowed(node, f"{type(node).__name__} statement")


def check_syntax_classdef(node: ast.ClassDef) -> None:
    if any(isinstance(b, ast.Name) and b.id == "Enum" for b in node.bases):
        raise NotAllowed(node, "enum classes")
    check_syntax_type_params(node)
    if len(node.decorator_list) == 0:
        raise NotAllowed(node, "undecorated class")
    if len(node.decorator_list) > 1:
        raise NotAllowed(node, "multiple class decorators")
    deco = node.decorator_list[0]
    if not (isinstance(deco, ast.Name) and deco.id == "dataclass"):
        raise NotAllowed(node, "class decorator other than @dataclass")
    if len(node.bases) > 1:
        raise NotAllowed(node, "multiple inheritance")
    if len(node.bases) > 0:
        base = node.bases[0]
        if not isinstance(ty_expr(base), Syntax.TyExprName):
            raise NotAllowed(
                base, "base class other than a name, optionally applied to type arguments"
            )
    if len(node.keywords) > 0:
        raise NotAllowed(node, "class keyword arguments")
    if not (len(node.body) == 1 and isinstance(node.body[0], ast.Pass)):
        for stmt in node.body:
            check_syntax_field(stmt)


def check_syntax_type_alias(node: ast.TypeAlias) -> None:
    check_syntax_type_params(node)
    check_syntax_annotation(node.value)


def duplicate[T](xs: Sequence[T]) -> T | None:
    """An element occurring twice in xs, if any"""
    return next((x for i, x in enumerate(xs) if x in xs[:i]), None)


def check_syntax_type_params(node: ast.FunctionDef | ast.ClassDef | ast.TypeAlias) -> None:
    dup = duplicate(
        [
            param.name
            for param in node.type_params
            if isinstance(param, (ast.TypeVar, ast.ParamSpec, ast.TypeVarTuple))
        ]
    )
    if dup is not None:
        raise NotAllowed(node, f"duplicate type parameter {dup}")
    for param in node.type_params:
        match param:
            case ast.TypeVar():
                if isinstance(param.bound, ast.Tuple):
                    raise NotAllowed(param, f"constraints on type parameter {param.name}")
                if param.bound is not None:
                    raise NotAllowed(param, f"bound on type parameter {param.name}")
            case ast.ParamSpec():
                raise NotAllowed(param, f"ParamSpec type parameter **{param.name}")
            case ast.TypeVarTuple():
                raise NotAllowed(param, f"TypeVarTuple type parameter *{param.name}")
            case _:
                raise AssertionError(f"unexpected type parameter: {type(param).__name__}")


def check_syntax_field(stmt: ast.stmt) -> None:
    if not isinstance(stmt, ast.AnnAssign):
        raise NotAllowed(stmt, "dataclass member other than a field declaration")
    if not isinstance(stmt.target, ast.Name):
        raise NotAllowed(stmt, "field target other than a simple name")
    if stmt.value is not None:
        raise NotAllowed(stmt, "field default values")
    check_syntax_annotation(stmt.annotation)


def check_syntax_pattern(node: ast.pattern) -> None:
    match node:
        case ast.MatchValue():
            v = node.value
            match v:
                case ast.Constant():
                    if isinstance(v.value, (int, float, str)):
                        return
                case ast.Attribute():
                    raise NotAllowed(node, "attribute value patterns")
            raise NotAllowed(node, "complex and bytes literal patterns")
        case ast.MatchSingleton():
            pass
        case ast.MatchAs():
            if node.pattern is not None:
                check_syntax_pattern(node.pattern)
        case PatList() | PatTuple():
            for p in node.patterns:
                check_syntax_pattern(p)
        case ast.MatchClass():
            for p in list(node.patterns) + list(node.kwd_patterns):
                check_syntax_pattern(p)
            dup = duplicate(node.kwd_attrs)
            if dup is not None:
                raise NotAllowed(node, f"duplicate keyword {dup} in constructor pattern")
        case ast.MatchMapping():
            if node.rest is not None:
                raise NotAllowed(node, "rest capture in dictionary patterns")
            for key in node.keys:
                if not (isinstance(key, ast.Constant) and isinstance(key.value, str)):
                    raise NotAllowed(key, "dictionary pattern key other than a string literal")
            dup = duplicate(
                [
                    key.value
                    for key in node.keys
                    if isinstance(key, ast.Constant) and isinstance(key.value, str)
                ]
            )
            if dup is not None:
                raise NotAllowed(node, f"duplicate key '{dup}' in dictionary pattern")
            for sub in node.patterns:
                check_syntax_pattern(sub)
        case ast.MatchOr():
            raise NotAllowed(node, "or-patterns")
        case ast.MatchStar():
            raise NotAllowed(node, "star patterns")
        case _:
            raise NotAllowed(node, f"{type(node).__name__} pattern")


def check_syntax_expr(node: ast.expr) -> None:
    match node:
        case ast.Constant():
            if isinstance(node.value, (int, float, str, bool, type(None))):
                return
            raise NotAllowed(node, f"{type(node.value).__name__} literal")
        case ast.Name():
            pass
        case ast.BinOp():
            allowed = (
                ast.Add,
                ast.Sub,
                ast.Mult,
                ast.Div,
                ast.FloorDiv,
                ast.Mod,
                ast.Pow,
                ast.BitOr,
            )
            if not isinstance(node.op, allowed):
                sym = OP_SYMBOLS.get(type(node.op), type(node.op).__name__)
                raise NotAllowed(node, f"binary operator '{sym}'")
            check_syntax_expr(node.left)
            check_syntax_expr(node.right)
        case ast.UnaryOp():
            if isinstance(node.op, (ast.Not, ast.UAdd, ast.USub)):
                check_syntax_expr(node.operand)
                return
            sym = OP_SYMBOLS.get(type(node.op), type(node.op).__name__)
            raise NotAllowed(node, f"unary operator '{sym}'")
        case ast.BoolOp():
            if len(node.values) > 2:
                raise NotAllowed(node, "chained boolean operator")
            for v in node.values:
                check_syntax_expr(v)
        case ast.Compare():
            if len(node.ops) > 1:
                raise NotAllowed(node, "chained comparison")
            for op in node.ops:
                if isinstance(op, (ast.Is, ast.IsNot)):
                    raise NotAllowed(node, "identity operator (is/is not)")
            check_syntax_expr(node.left)
            for c in node.comparators:
                check_syntax_expr(c)
        case ast.Call():
            check_syntax_expr(node.func)
            for a in node.args:
                check_syntax_expr(a)
            for k in node.keywords:
                if k.arg is None:
                    raise NotAllowed(k, "dictionary unpacking in argument list")
                check_syntax_expr(k.value)
            dup = duplicate([k.arg for k in node.keywords])
            if dup is not None:
                raise NotAllowed(node, f"duplicate keyword argument {dup}")
        case ast.IfExp():
            check_syntax_expr(node.test)
            check_syntax_expr(node.body)
            check_syntax_expr(node.orelse)
        case ast.Lambda():
            check_syntax_arguments(node.args)
            check_syntax_expr(node.body)
        case ast.List() | ast.Tuple():
            for e in node.elts:
                check_syntax_expr(e)
        case ast.Dict():
            for key in node.keys:
                if key is None:
                    raise NotAllowed(node, "dictionary unpacking")
                check_syntax_expr(key)
            for v in node.values:
                check_syntax_expr(v)
        case ast.Set():
            raise NotAllowed(node, "set literals")
        case ast.Attribute():
            check_syntax_expr(node.value)
        case ast.Subscript():
            check_syntax_expr(node.value)
            check_syntax_expr(node.slice)
        case ast.ListComp():
            check_syntax_expr(node.elt)
            for g in node.generators:
                check_syntax_generator(g)
        case ast.DictComp():
            check_syntax_expr(node.key)
            check_syntax_expr(node.value)
            for g in node.generators:
                check_syntax_generator(g)
        case ast.SetComp():
            raise NotAllowed(node, "set comprehensions")
        case ast.Slice():
            raise NotAllowed(node, "slicing")
        case ast.GeneratorExp():
            raise NotAllowed(node, "generator expressions")
        case ast.NamedExpr():
            raise NotAllowed(node, "walrus operator (:=)")
        case ast.Starred():
            raise NotAllowed(node, "starred expressions")
        case ast.Await():
            raise NotAllowed(node, "async")
        case ast.Yield() | ast.YieldFrom():
            raise NotAllowed(node, "yield")
        case ast.JoinedStr() | ast.FormattedValue():
            raise NotAllowed(node, "f-strings")
        case _:
            raise NotAllowed(node, f"{type(node).__name__} expression")


def check_syntax_body(stmts: list[ast.stmt]) -> None:
    for s in stmts:
        check_syntax_stmt(s)


def check_syntax_import(node: ast.stmt) -> None:
    match node:
        case ast.Import():
            if len(node.names) != 1:
                raise NotAllowed(node, "multi-target import (import a, b)")
            if node.names[0].asname is not None:
                raise NotAllowed(node, "import-as")
        case ast.ImportFrom():
            if len(node.names) == 0:
                raise NotAllowed(node, "empty name list")
            if node.level > 0:
                raise NotAllowed(node, "relative imports")
            assert node.module is not None  # absent only in a relative import
            for alias in node.names:
                if alias.name == "*":
                    raise NotAllowed(node, "from M import *")
                if alias.asname is not None:
                    raise NotAllowed(node, "from-import-as")
        case _:
            raise AssertionError(f"unexpected statement: {type(node).__name__}")


def check_syntax_top_level(body: list[ast.stmt]) -> None:
    iotas, stmts = split_imports(body)
    for iota in iotas:
        check_syntax_import(iota)
    for s in stmts:
        if is_import(s):
            raise NotAllowed(s, "import after another statement")
        for ret in returns_outside_function(s):
            raise NotAllowed(ret, "return outside a function")
        if isinstance(s, ast.ClassDef):
            check_syntax_classdef(s)
        elif isinstance(s, ast.TypeAlias):
            check_syntax_type_alias(s)
        else:
            check_syntax_stmt(s)


def returns_outside_function(s: ast.stmt) -> list[ast.Return]:
    """Return statements of a top-level statement s, which Python rejects when compiling a module"""
    match s:
        case ast.Return():
            return [s]
        case ast.If(body=ss, orelse=ss_):
            return [r for s_ in ss + ss_ for r in returns_outside_function(s_)]
        case ast.Match(cases=cases):
            return [r for case in cases for s_ in case.body for r in returns_outside_function(s_)]
        case _:
            return []


def check_syntax_generator(node: ast.comprehension) -> None:
    if node.is_async:
        raise NotAllowed(node, "async comprehensions")
    if not isinstance(node.target, ast.Name):
        raise NotAllowed(node, "unpacking in comprehensions")
    check_syntax_expr(node.iter)
    for i in node.ifs:
        check_syntax_expr(i)


def check_syntax_annotation(node: ast.expr | None) -> None:
    if node is None:
        return
    if ty_expr(node) is None:
        raise NotAllowed(node, "annotation that is not a type expression")


def check_syntax_arguments(node: ast.arguments) -> None:
    if node.vararg is not None:
        raise NotAllowed(node, "*args")
    if node.kwarg is not None:
        raise NotAllowed(node, "**kwargs")
    if len(node.kwonlyargs) > 0:
        raise NotAllowed(node, "keyword-only arguments")
    if len(node.defaults) > 0:
        raise NotAllowed(node, "default arguments")
    if len(node.kw_defaults) > 0:
        raise NotAllowed(node, "default arguments")
    if len(node.posonlyargs) > 0:
        raise NotAllowed(node, "positional-only arguments")
    for a in node.args:
        check_syntax_annotation(a.annotation)
    dup = duplicate([a.arg for a in node.args])
    if dup is not None:
        raise NotAllowed(node, f"duplicate parameter {dup}")


def check_syntax_module(node: ast.Module) -> Unsupported | None:
    try:
        check_syntax_top_level(node.body)
        return None
    except Unsupported as e:
        return e


def format_result(result: Unsupported | None, filename: str) -> str:
    if result is None:
        return f"{filename}: ok"
    if result.line is not None:
        return f"{filename}:{result.line}:{result.col}: {result.msg}"
    return f"{filename}: {result.msg}"


def option(x: Any) -> Any:
    return Option.None_() if x is None else Option.Some(x)


def position(node: ast.expr | ast.stmt | ast.pattern) -> tuple[int, int]:
    return (node.lineno, node.col_offset)


def at(node: ast.expr | ast.stmt | ast.pattern, term: Any) -> Any:
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


def lit(v: object) -> Lit:
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


def name(e: ast.expr) -> Name | None:
    match e:
        case ast.Name(id=x):
            return (x,)
        case ast.Attribute(value=e_, attr=x):
            q = name(e_)
            return None if q is None else (*q, x)
        case _:
            return None


def qualified_name(q: Name) -> QualifiedName:
    return (q[0], list(q[1:]))


PRIM_TY = {
    "object": Syntax.object_,
    "Never": Syntax.Never,
    "None": Syntax.NoneType,
    "bool": Syntax.bool_,
    "int": Syntax.int_,
    "float": Syntax.float_,
    "str": Syntax.str_,
    "Sized": Syntax.Sized,
}
PRIMITIVE = {c: x for x, c in PRIM_TY.items()}


def ty_expr(e: ast.expr) -> TyExpr | None:
    match e:
        case ast.Constant(value=None):
            return Syntax.TyExprPrim(Syntax.NoneType())
        case ast.Name(id=x) if x in PRIM_TY:
            return Syntax.TyExprPrim(PRIM_TY[x]())
        case ast.Name() | ast.Attribute():
            q = name(e)
            return None if q is None else Syntax.TyExprName(qualified_name(q), [])
        case ast.BinOp(left=e1, op=ast.BitOr(), right=e2):
            psi, psi_ = ty_expr(e1), ty_expr(e2)
            return None if psi is None or psi_ is None else Syntax.TyExprUnion(psi, psi_)
        case ast.Subscript(value=ast.Name(id="Literal"), slice=s):
            match s:
                case ast.Constant(value=bool() | int() | str() | None as v):
                    return Syntax.TyExprLiteral(lit(v))
                case _:
                    return None
        case ast.Subscript(value=ast.Name(id="Callable"), slice=s):
            match s:
                case ast.Tuple(elts=[ast.List(elts=es), e_]):
                    psis, psi = ty_exprs(es), ty_expr(e_)
                    return None if psis is None or psi is None else Syntax.TyExprCallable(psis, psi)
                case _:
                    return None
        case ast.Subscript(value=head, slice=s):
            psis = ty_exprs(s.elts if isinstance(s, ast.Tuple) else [s])
            if psis is None:
                return None
            match head, psis:
                case ast.Name(id="list"), [psi]:
                    return Syntax.TyExprList(psi)
                case ast.Name(id="list"), _:
                    return None
                case ast.Name(id="tuple"), _:
                    return Syntax.TyExprTuple(psis)
                case ast.Name(id="dict"), [Syntax.TyExprPrim(Syntax.str_()), psi]:
                    return Syntax.TyExprDict(psi)
                case ast.Name(id="dict"), _:
                    return None
                case _:
                    q = name(head)
                    return None if q is None else Syntax.TyExprName(qualified_name(q), psis)
        case _:
            return None


def ty_exprs(es: list[ast.expr]) -> list[TyExpr] | None:
    psis = [ty_expr(e) for e in es]
    return None if any(psi is None for psi in psis) else psis


def annotation(e: ast.expr | None) -> TyExpr:
    psi = None if e is None else ty_expr(e)
    assert psi is not None  # missing and malformed annotations rejected by the parser
    return psi


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
BOP_AST = {bop: op for op, bop in BOP.items()}
UOP_AST = {uop: op for op, uop in UOP.items()}


def expr(e: ast.expr) -> Expr:
    return at(e, expr_node(e))


def expr_node(e: ast.expr) -> Expr:
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


def keyword(k: ast.keyword) -> tuple[str, Expr]:
    assert k.arg is not None  # dictionary unpacking rejected by the parser
    return (k.arg, expr(k.value))


# A generator is located at its target, since the parsed form has no position for the generator itself
def qualifiers(gs: list[ast.comprehension]) -> list[Qualifier]:
    return [
        q
        for g in gs
        for q in [
            at(g.target, Syntax.Generator(target_name(g), expr(g.iter))),
            *(at(c, Syntax.Guard(expr(c))) for c in g.ifs),
        ]
    ]


def pat(p: ast.pattern) -> Pat:
    return at(p, pat_node(p))


def pat_node(p: ast.pattern) -> Pat:
    match p:
        case ast.MatchValue(value=ast.Constant(value=v)) | ast.MatchSingleton(value=v):
            return Syntax.PatLiteral(lit(v))
        case ast.MatchAs(pattern=None, name=None):
            return Syntax.PatWildcard()
        case ast.MatchAs(pattern=None, name=str(x)):
            return Syntax.PatVar(x)
        case ast.MatchAs(pattern=ast.pattern() as p_, name=str(x)):
            return Syntax.PatAs(pat(p_), x)
        case PatList(patterns=ps):
            return Syntax.PatList([pat(p_) for p_ in ps])
        case PatTuple(patterns=ps):
            return Syntax.PatTuple([pat(p_) for p_ in ps])
        case ast.MatchClass(cls=c, patterns=ps, kwd_attrs=xs, kwd_patterns=qs):
            q = name(c)
            assert q is not None  # other heads rejected by Python
            return Syntax.PatConstr(
                qualified_name(q), ([pat(p_) for p_ in ps], [(x, pat(q_)) for x, q_ in zip(xs, qs)])
            )
        case ast.MatchMapping(keys=ks, patterns=ps):
            return Syntax.PatDict([(key(k), pat(q)) for k, q in zip(ks, ps)])
        case _:
            raise AssertionError(f"unexpected pattern: {type(p).__name__}")


def key(k: ast.expr) -> str:
    assert isinstance(k, ast.Constant) and isinstance(k.value, str)  # others rejected by the parser
    return k.value


def stmt(s: ast.stmt) -> Stmt:
    return at(s, stmt_node(s))


def stmt_node(s: ast.stmt) -> Stmt:
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


def branches(col: int, orelse: list[ast.stmt]) -> tuple[list[tuple[Expr, Stmt]], Any]:
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


def seq(body: list[ast.stmt]) -> Stmt:
    *items, item = statements(body)
    return reduce(lambda s, item_: seq_stmt(item_stmt(item_), s), reversed(items), item_stmt(item))


def seq_stmt(s: Stmt, s_: Stmt) -> Stmt:
    return Positions.At(located_at(s), Syntax.StmtSeq(s, s_))


def item_stmt(item: Statement) -> Stmt:
    match item:
        case ast.stmt():
            return stmt(item)
        case [ast.FunctionDef() as d, *_]:
            return at(d, Syntax.StmtMutualRegion([func(d_) for d_ in item]))
        case _:
            raise AssertionError("type definition outside the module top level")


def func(d: ast.stmt) -> Func:
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


def type_params(node: ast.FunctionDef | ast.ClassDef | ast.TypeAlias) -> list[str]:
    return [alpha for alpha in type_param_names(node)]


def type_def(chi: ast.stmt) -> TypeDef:
    return at(chi, type_def_node(chi))


def type_def_node(chi: ast.stmt) -> TypeDef:
    match chi:
        case ast.ClassDef(name=c, bases=bases, body=body):
            fields = [
                (t.target.id, annotation(t.annotation))
                for t in body
                if isinstance(t, ast.AnnAssign) and isinstance(t.target, ast.Name)
            ]
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
            match ty_expr(b):
                case Syntax.TyExprName(q, args):
                    return Option.Some((q, args))
                case _:
                    raise AssertionError("base class rejected by the parser")
        case _:
            raise AssertionError("multiple inheritance")


def top_stmt(body: list[ast.stmt]) -> TopStmt:
    *items, item = statements(body)
    return reduce(
        lambda s, item_: Syntax.TopSeq(top_item(item_), s), reversed(items), top_item(item)
    )


def top_item(item: Statement) -> TopStmt:
    match item:
        case [ast.ClassDef() | ast.TypeAlias(), *_]:
            return Syntax.TypeDefs([type_def(chi) for chi in item])
        case _:
            return Syntax.Stmt(item_stmt(item))


def import_(iota: ast.stmt) -> Import:
    return at(iota, import_node(iota))


def import_node(iota: ast.stmt) -> Import:
    match iota:
        case ast.Import(names=[alias]):
            return Syntax.Import(qualified_name(parse_name(alias.name)))
        case ast.ImportFrom(module=str(q), names=aliases):
            return Syntax.FromImport(qualified_name(parse_name(q)), [a.name for a in aliases])
        case _:
            raise AssertionError(f"unexpected import: {type(iota).__name__}")


NAME = "__name__"


def name_declaration(q: Name) -> ast.AnnAssign:
    return ast.AnnAssign(
        target=ast.Name(id=NAME, ctx=ast.Store()),
        annotation=ast.Name(id="str", ctx=ast.Load()),
        value=ast.Constant(value=".".join(q)),
        simple=1,
        lineno=1,
        col_offset=0,
    )


def module_body(q: Name, m: ast.Module) -> ModuleBody:
    iotas, stmts = split_imports(m.body)
    imports = [import_(iota) for iota in iotas]
    return Syntax.ModuleBody(
        imports, top_stmt([ast.fix_missing_locations(name_declaration(q)), *stmts])
    )


def parse_module(source: str, filename: str, q: Name) -> ModuleBody:
    """Body of module q in the generated syntax, or Unsupported raised for a source outside the fragment"""
    try:
        m = parse(source, filename)
    except SyntaxError as e:
        raise ParseError(e) from e
    check_syntax_top_level(m.body)
    return module_body(q, m)

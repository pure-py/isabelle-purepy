"""Module loading, imports and programs, against the generated evaluator"""

from basic_tests import chars, lit, lookup, var
from constr_tests import EQ_NAME, call

from purepy.generated import Eval, Finite_Map, Option, Semantics, Syntax

MAIN = (chars("__main__"), [])


def name(*xs):
    return (chars(xs[0]), [chars(x) for x in xs[1:]])


def program(*modules):
    """Program of (name, imports, statements) triples"""
    m = Finite_Map.fmempty
    for q, imports, stmts in modules:
        m = Finite_Map.fmupd(EQ_NAME, q, Syntax.ModuleBody(imports, top(*stmts)), m)
    return m


def top(*stmts):
    ts = [Syntax.Stmt(s) for s in stmts] or [Syntax.Stmt(Syntax.StmtPass())]
    t = ts[-1]
    for s in reversed(ts[:-1]):
        t = Syntax.TopSeq(s, t)
    return t


def assign(x, e):
    return Syntax.StmtAssign(chars(x), Option.None_(), e)


def attr(e, *xs):
    for x in xs:
        e = Syntax.ExprAttribute(e, chars(x))
    return e


def run(m, fuel=50):
    return Eval.run_program(Finite_Map.fmempty, m, ["main.py"], fuel)


def main_env(m):
    match Eval.run_mod(Finite_Map.fmempty, m, ["main.py"], 50, MAIN):
        case Eval.Done(Semantics.Val(rho)):
            return rho
    raise AssertionError("main does not load")


def int_val(n):
    return Option.Some(Semantics.VLit(Syntax.LitInt(n)))


DIV0 = Syntax.ExprBinOp(Syntax.BOpFloorDiv(), lit(1), lit(0))


def test_eval_program():
    m = program((MAIN, [], [assign("r", lit(1))]))
    assert run(m) == Eval.Done(Semantics.SystemExit_(0))
    assert lookup(main_env(m), "r") == int_val(1)


def test_eval_import():
    """import m; r = m.a"""
    m = program(
        (MAIN, [Syntax.Import(name("m"))], [assign("r", attr(var("m"), "a"))]),
        (name("m"), [], [assign("a", lit(1))]),
    )
    assert lookup(main_env(m), "r") == int_val(1)


def test_eval_import_submodules():
    """import p.q; r = p.q.x, loading p and then p.q"""
    m = program(
        (MAIN, [Syntax.Import(name("p", "q"))], [assign("r", attr(var("p"), "q", "x"))]),
        (name("p"), [], []),
        (name("p", "q"), [], [assign("x", lit(2))]),
    )
    assert lookup(main_env(m), "r") == int_val(2)


def test_eval_from_import():
    """from m import a; from p import q, the submodule loaded through its stub"""
    m = program(
        (
            MAIN,
            [
                Syntax.FromImport(name("m"), [chars("a")]),
                Syntax.FromImport(name("p"), [chars("q")]),
            ],
            [assign("r", var("a")), assign("s", attr(var("q"), "x"))],
        ),
        (name("m"), [], [assign("a", lit(1))]),
        (name("p"), [], []),
        (name("p", "q"), [], [assign("x", lit(2))]),
    )
    rho = main_env(m)
    assert lookup(rho, "r") == int_val(1)
    assert lookup(rho, "s") == int_val(2)


def test_eval_predefined():
    """from sys import exit; exit(3): the program exits with 3; len is a builtin; __name__ of a predefined module"""
    m = program(
        (
            MAIN,
            [Syntax.FromImport(name("sys"), [chars("exit")])],
            [Syntax.StmtExpr(call(var("exit"), [lit(3)]))],
        )
    )
    assert run(m) == Eval.Done(Semantics.SystemExit_(3))
    m = program(
        (
            MAIN,
            [Syntax.Import(name("sys"))],
            [
                assign("r", call(var("len"), [Syntax.ExprList([lit(1), lit(2)])])),
                assign("s", attr(var("sys"), "__name__")),
            ],
        )
    )
    rho = main_env(m)
    assert lookup(rho, "r") == int_val(2)
    assert lookup(rho, "s") == Option.Some(Semantics.VLit(Syntax.LitString(chars("sys"))))


def test_eval_program_abort():
    """An abort in an imported module aborts the program"""
    m = program(
        (MAIN, [Syntax.Import(name("m"))], [assign("r", lit(1))]),
        (name("m"), [], [assign("a", DIV0)]),
    )
    assert run(m) == Eval.Done(Semantics.ZeroDivisionError_())
    m = program(
        (MAIN, [Syntax.FromImport(name("m"), [chars("a")])], []),
        (name("m"), [], [assign("a", DIV0)]),
    )
    assert run(m) == Eval.Done(Semantics.ZeroDivisionError_())


def test_eval_import_cycle():
    """An import cycle has no derivation, and runs out of fuel"""
    m = program((MAIN, [Syntax.Import(name("m"))], []), (name("m"), [Syntax.Import(MAIN)], []))
    assert run(m) == Eval.OutOfFuel()

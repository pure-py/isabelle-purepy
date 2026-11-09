"""Module loading, imports and programs, against the generated evaluator, observed through what they print"""

from basic_tests import chars, lit, name, var
from constr_tests import EQ_NAME, call

from purepy.generated import Eval, Finite_Map, Option, Syntax, Values

MAIN = Syntax.main()


def program(*modules):
    """Program of (name, imports, statements) triples"""
    m = Finite_Map.fmempty()
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
    return Eval.run_program(Finite_Map.fmempty(), m, fuel, ["main.py"])


def exits(vs, kappa):
    return Eval.Done((vs, kappa))


def ints(*ns):
    return [Values.VLit(Syntax.LitInt(n)) for n in ns]


OK = Values.SystemExit_(0)
DIV0 = Syntax.ExprBinOp(Syntax.BOpFloorDiv(), lit(1), lit(0))


def test_eval_program():
    m = program((MAIN, [], [assign("r", lit(1)), Syntax.StmtPrint(var("r"))]))
    assert run(m) == exits(ints(1), OK)


def test_eval_import():
    """import m; print(m.a), m printing first"""
    m = program(
        (MAIN, [Syntax.Import(name("m"))], [Syntax.StmtPrint(attr(var("m"), "a"))]),
        (name("m"), [], [assign("a", lit(1)), Syntax.StmtPrint(lit(0))]),
    )
    assert run(m) == exits(ints(0, 1), OK)


def test_eval_import_submodules():
    """import p.q; print(p.q.x), loading p and then p.q"""
    m = program(
        (MAIN, [Syntax.Import(name("p", "q"))], [Syntax.StmtPrint(attr(var("p"), "q", "x"))]),
        (name("p"), [], []),
        (name("p", "q"), [], [assign("x", lit(2))]),
    )
    assert run(m) == exits(ints(2), OK)


def test_eval_from_import():
    """from m import a; from p import q, the submodule loaded through its stub"""
    m = program(
        (
            MAIN,
            [
                Syntax.FromImport(name("m"), [chars("a")]),
                Syntax.FromImport(name("p"), [chars("q")]),
            ],
            [Syntax.StmtPrint(var("a")), Syntax.StmtPrint(attr(var("q"), "x"))],
        ),
        (name("m"), [], [assign("a", lit(1))]),
        (name("p"), [], []),
        (name("p", "q"), [], [assign("x", lit(2))]),
    )
    assert run(m) == exits(ints(1, 2), OK)


def test_eval_predefined():
    """from sys import exit; exit(3): the program exits with 3; len is a builtin; __name__ of a predefined module"""
    m = program(
        (
            MAIN,
            [Syntax.FromImport(name("sys"), [chars("exit")])],
            [Syntax.StmtExpr(call(var("exit"), [lit(3)]))],
        )
    )
    assert run(m) == exits([], Values.SystemExit_(3))
    m = program(
        (
            MAIN,
            [Syntax.Import(name("sys"))],
            [
                Syntax.StmtPrint(call(var("len"), [Syntax.ExprList([lit(1), lit(2)])])),
                Syntax.StmtPrint(attr(var("sys"), "__name__")),
            ],
        )
    )
    assert run(m) == exits([*ints(2), Values.VLit(Syntax.LitString(chars("sys")))], OK)


def test_eval_program_abort():
    """An abort in an imported module aborts the program, after what it printed"""
    m = program(
        (MAIN, [Syntax.Import(name("m"))], [Syntax.StmtPrint(lit(1))]),
        (name("m"), [], [Syntax.StmtPrint(lit(0)), assign("a", DIV0)]),
    )
    assert run(m) == exits(ints(0), Values.ZeroDivisionError_())
    m = program(
        (MAIN, [Syntax.FromImport(name("m"), [chars("a")])], []),
        (name("m"), [], [assign("a", DIV0)]),
    )
    assert run(m) == exits([], Values.ZeroDivisionError_())


def test_eval_import_cycle():
    """An import cycle has no order of loading, and runs out of fuel"""
    m = program((MAIN, [Syntax.Import(name("m"))], []), (name("m"), [Syntax.Import(MAIN)], []))
    assert run(m) == Eval.OutOfFuel()

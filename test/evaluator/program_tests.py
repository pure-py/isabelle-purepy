"""Programs, at an import cycle, which typing rules out"""

from basic_tests import name
from constr_tests import EQ_NAME

from purepy.generated import Eval, Finite_Map, Syntax

MAIN = Syntax.main


def program(*modules):
    """Program of (name, imports) pairs, each module with an empty body"""
    m = Finite_Map.fmempty
    for q, imports in modules:
        body = Syntax.ModuleBody(imports, Syntax.Stmt(Syntax.StmtPass()))
        m = Finite_Map.fmupd(EQ_NAME, q, body, m)
    return m


def test_eval_import_cycle():
    """An import cycle has no order of loading, and runs out of fuel"""
    m = program((MAIN, [Syntax.Import(name("m"))]), (name("m"), [Syntax.Import(MAIN)]))
    assert Eval.run_program(Finite_Map.fmempty, m, 50, ["main.py"]) == Eval.OutOfFuel()

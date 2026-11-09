"""Top-level statements, at a return, which typing rules out"""

from basic_tests import chars, lit, name, ret
from constr_tests import SIGMA

from purepy.generated import Eval, Finite_Map, Option, Syntax, Values

M = name("m")


def assign(x, e):
    return Syntax.Stmt(Syntax.StmtAssign(chars(x), Option.None_(), e))


def top_seq(t, *ts):
    return Syntax.TopSeq(t, top_seq(*ts)) if ts else t


def run(t):
    return Eval.run_top(SIGMA, 50, M, Finite_Map.fmempty(), t)


def test_eval_top_stmt_return():
    """A return as the last statement is evaluated by the statement judgement; before another, no rule applies"""
    assert run(Syntax.Stmt(ret(lit(1)))) == Eval.Done(
        ([], Values.Returns(Values.VLit(Syntax.LitInt(1))))
    )
    assert run(top_seq(Syntax.Stmt(ret(lit(1))), assign("r", lit(1)))) == Eval.Stuck()

"""Top-level statements, against the generated evaluator"""

from basic_tests import chars, lit, lookup, ret, var
from constr_tests import BOX, SIGMA, call

from purepy.generated import Eval, Finite_Map, Option, Semantics, Syntax

M = (chars("m"), [])
INT = Syntax.TyExprPrim(Syntax.int_())
BOX_DEF = Syntax.Dataclass(chars("Box"), [], Option.None_(), [(chars("x"), INT), (chars("y"), INT)])
PAIR_DEF = Syntax.TypeStmt(chars("Pair"), [], Syntax.TyExprName((chars("tuple"), []), [INT, INT]))
DIV0 = Syntax.ExprBinOp(Syntax.BOpFloorDiv(), lit(1), lit(0))


def assign(x, e):
    return Syntax.Stmt(Syntax.StmtAssign(chars(x), Option.None_(), e))


def top_seq(t, *ts):
    return Syntax.TopSeq(t, top_seq(*ts)) if ts else t


def run(t):
    return Eval.run_top(SIGMA, 50, M, Finite_Map.fmempty, t)


def env_of(r):
    match r:
        case Eval.Done(Semantics.Assigns(delta)):
            return delta
    raise AssertionError(r)


def test_eval_types():
    """A class binds its name to the class value, an alias to an alias value recording the region"""
    delta = env_of(run(Syntax.TypeDefs([BOX_DEF, PAIR_DEF])))
    assert lookup(delta, "Box") == Option.Some(Semantics.VClass(BOX))
    assert lookup(delta, "Pair") == Option.Some(Semantics.VTypeAlias(M, [BOX_DEF, PAIR_DEF], 1))


def test_eval_top_seq():
    """class Box ...; b = Box(1, 2); r = b.y: the class is bound for the statements that follow"""
    t = top_seq(
        Syntax.TypeDefs([BOX_DEF]),
        assign("b", call(var("Box"), [lit(1), lit(2)])),
        assign("r", Syntax.ExprAttribute(var("b"), chars("y"))),
    )
    assert lookup(env_of(run(t)), "r") == Option.Some(Semantics.VLit(Syntax.LitInt(2)))


def test_eval_top_seq_fail():
    """An abort skips the rest"""
    t = top_seq(assign("a", DIV0), assign("r", lit(1)))
    assert run(t) == Eval.Done(Semantics.Aborts_o(Semantics.ZeroDivisionError_()))


def test_eval_top_stmt_return():
    """A return as the last statement is evaluated by the statement judgement; before another, no rule applies"""
    assert run(Syntax.Stmt(ret(lit(1)))) == Eval.Done(
        Semantics.Returns(Semantics.VLit(Syntax.LitInt(1)))
    )
    assert run(top_seq(Syntax.Stmt(ret(lit(1))), assign("r", lit(1)))) == Eval.Stuck()

"""Constructor patterns, at the aborting cases which typing rules out"""

from basic_tests import aborts_o, chars, lit, lookup, name, var
from constr_tests import BOX, EQ_NAME, EQ_VAR, GAMMA, call

from purepy.generated import Contexts, Eval, Finite_Map, Option, Syntax, Values

SUB = name("m", "Sub")
INT = Syntax.TyExprPrim(Syntax.int_())
# @dataclass class Box: x: int; y: int
# @dataclass class Sub(Box): z: int
DECLS = [
    Syntax.Dataclass(chars("Box"), [], Option.None_(), [(chars("x"), INT), (chars("y"), INT)]),
    Syntax.Dataclass(chars("Sub"), [], Option.Some((name("Box"), [])), [(chars("z"), INT)]),
]
SIGMA = Finite_Map.fmupd(
    EQ_NAME,
    SUB,
    Contexts.ClassDef(GAMMA, name("m"), DECLS, 1),
    Finite_Map.fmupd(
        EQ_NAME, BOX, Contexts.ClassDef(GAMMA, name("m"), DECLS, 0), Finite_Map.fmempty()
    ),
)
RHO = Finite_Map.fmupd(
    EQ_VAR,
    chars("Sub"),
    Values.VClass(SUB),
    Finite_Map.fmupd(
        EQ_VAR,
        chars("Box"),
        Values.VClass(BOX),
        Finite_Map.fmupd(EQ_VAR, chars("n"), Values.VLit(Syntax.LitInt(0)), Finite_Map.fmempty()),
    ),
)


def pvar(x):
    return Syntax.PatVar(chars(x))


def pconstr(c, ps, kps=()):
    return Syntax.PatConstr(name(c), (list(ps), [(chars(y), p) for y, p in kps]))


def assign(x, e):
    return Syntax.StmtAssign(chars(x), Option.None_(), e)


def run_match(e, p):
    """match e: case p: r = (a, b) | case _: r = 0, giving r, or the outcome if it is not Assigns"""
    pair = Syntax.ExprTuple([var("a"), var("b")])
    s = Syntax.StmtMatch(e, [(p, assign("r", pair)), (Syntax.PatWildcard(), assign("r", lit(0)))])
    match Eval.run_stmt(SIGMA, 50, RHO, s):
        case Eval.Done(([], Values.Assigns(delta))):
            return lookup(delta, "r")
        case o:
            return o


BOX12 = call(var("Box"), [lit(1), lit(2)])


def aborts(k):
    return Eval.Done(aborts_o(k))


def test_eval_match_constr_type_error():
    """Too many positional sub-patterns, a keyword for a positional field, or a head that is not a class"""
    assert run_match(BOX12, pconstr("Box", [pvar("a"), pvar("b"), pvar("c")])) == aborts(
        Values.TypeError_()
    )
    assert run_match(BOX12, pconstr("Box", [pvar("a")], [("x", pvar("b"))])) == aborts(
        Values.TypeError_()
    )
    assert run_match(BOX12, pconstr("n", [])) == aborts(Values.TypeError_())


def test_eval_match_constr_excluded():
    """Sub-patterns not covering the fields, which Python allows"""
    assert run_match(BOX12, pconstr("Box", [pvar("a")])) == aborts(Values.Excluded())
    assert run_match(BOX12, pconstr("Box", [], [("x", pvar("a"))])) == aborts(Values.Excluded())

"""Constructor patterns, against the generated evaluator"""

from basic_tests import chars, lit, lookup, var
from constr_tests import BOX, EQ_NAME, EQ_VAR, GAMMA, call

from purepy.generated import Contexts, Eval, Finite_Map, Option, Semantics, Syntax

SUB = (chars("m"), [chars("Sub")])
INT = Syntax.TyExprPrim(Syntax.int_())
# @dataclass class Box: x: int; y: int
# @dataclass class Sub(Box): z: int
DECLS = [
    Syntax.Dataclass(chars("Box"), [], Option.None_(), [(chars("x"), INT), (chars("y"), INT)]),
    Syntax.Dataclass(chars("Sub"), [], Option.Some(((chars("Box"), []), [])), [(chars("z"), INT)]),
]
SIGMA = Finite_Map.fmupd(
    EQ_NAME,
    SUB,
    Contexts.ClassDef(GAMMA, (chars("m"), []), DECLS, 1),
    Finite_Map.fmupd(
        EQ_NAME, BOX, Contexts.ClassDef(GAMMA, (chars("m"), []), DECLS, 0), Finite_Map.fmempty
    ),
)
RHO = Finite_Map.fmupd(
    EQ_VAR,
    chars("Sub"),
    Semantics.VClass(SUB),
    Finite_Map.fmupd(
        EQ_VAR,
        chars("Box"),
        Semantics.VClass(BOX),
        Finite_Map.fmupd(EQ_VAR, chars("n"), Semantics.VLit(Syntax.LitInt(0)), Finite_Map.fmempty),
    ),
)


def pvar(x):
    return Syntax.PatVar(chars(x))


def pconstr(c, ps, kps=()):
    return Syntax.PatConstr((chars(c), []), (list(ps), [(chars(y), p) for y, p in kps]))


def assign(x, e):
    return Syntax.StmtAssign(chars(x), Option.None_(), e)


def run_match(e, p):
    """match e: case p: r = (a, b) | case _: r = 0, giving r, or the outcome if it is not Assigns"""
    pair = Syntax.ExprTuple([var("a"), var("b")])
    s = Syntax.StmtMatch(e, [(p, assign("r", pair)), (Syntax.PatWildcard(), assign("r", lit(0)))])
    match Eval.run_stmt(SIGMA, 50, RHO, s):
        case Eval.Done(Semantics.Assigns(delta)):
            return lookup(delta, "r")
        case o:
            return o


def pair(a, b):
    return Option.Some(
        Semantics.VTuple([Semantics.VLit(Syntax.LitInt(a)), Semantics.VLit(Syntax.LitInt(b))])
    )


NO_MATCH = Option.Some(Semantics.VLit(Syntax.LitInt(0)))
BOX12 = call(var("Box"), [lit(1), lit(2)])
SUB123 = call(var("Sub"), [lit(1), lit(2), lit(3)])


def aborts(k):
    return Eval.Done(Semantics.Aborts_o(k))


def test_eval_match_constr_positional_and_keywords():
    assert run_match(BOX12, pconstr("Box", [pvar("a"), pvar("b")])) == pair(1, 2)
    assert run_match(BOX12, pconstr("Box", [], [("y", pvar("b")), ("x", pvar("a"))])) == pair(1, 2)
    assert run_match(BOX12, pconstr("Box", [pvar("a")], [("y", pvar("b"))])) == pair(1, 2)


def test_eval_match_constr_subclass():
    """A Sub object matches Box(a, b), but a Box object does not match Sub(...)"""
    assert run_match(SUB123, pconstr("Box", [pvar("a"), pvar("b")])) == pair(1, 2)
    assert (
        run_match(BOX12, pconstr("Sub", [pvar("a"), pvar("b"), Syntax.PatWildcard()])) == NO_MATCH
    )


def test_eval_match_constr_no_match():
    """A non-object, or a sub-pattern that does not match"""
    assert run_match(lit(1), pconstr("Box", [pvar("a"), pvar("b")])) == NO_MATCH
    one = Syntax.PatLiteral(Syntax.LitInt(1))
    assert run_match(BOX12, pconstr("Box", [pvar("a"), one])) == NO_MATCH


def test_eval_match_constr_type_error():
    """Too many positional sub-patterns, a keyword for a positional field, or a head that is not a class"""
    assert run_match(BOX12, pconstr("Box", [pvar("a"), pvar("b"), pvar("c")])) == aborts(
        Semantics.TypeError_()
    )
    assert run_match(BOX12, pconstr("Box", [pvar("a")], [("x", pvar("b"))])) == aborts(
        Semantics.TypeError_()
    )
    assert run_match(BOX12, pconstr("n", [])) == aborts(Semantics.TypeError_())


def test_eval_match_constr_excluded():
    """Sub-patterns not covering the fields, which Python allows"""
    assert run_match(BOX12, pconstr("Box", [pvar("a")])) == aborts(Semantics.Excluded())
    assert run_match(BOX12, pconstr("Box", [], [("x", pvar("a"))])) == aborts(Semantics.Excluded())

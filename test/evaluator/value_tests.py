"""Primitives, module values and opaque values, at the aborting cases which typing rules out"""

from basic_tests import aborts_o, chars, lit, name, var
from constr_tests import BOX, EQ_VAR, SIGMA, aborts, call

from purepy.generated import Eval, Finite_Map, Option, Syntax, Values

M = name("m")


def env(*bindings):
    rho = Finite_Map.fmempty()
    for x, v in bindings:
        rho = Finite_Map.fmupd(EQ_VAR, chars(x), v, rho)
    return rho


def int_val(n):
    return Values.VLit(Syntax.LitInt(n))


MODULE = Values.VModLoaded(M, env(("a", int_val(1)), ("Box", Values.VClass(BOX))))
RHO = env(
    ("Box", Values.VClass(BOX)),
    ("len", Values.VPrim(Values.PrimLen())),
    ("round", Values.VPrim(Values.PrimRound())),
    ("exit", Values.VPrim(Values.PrimExit())),
    ("int", Values.VPredef(name("builtins", "int"))),
    ("Callable", Values.VPredef(name("typing", "Callable"))),
    ("m", MODULE),
    ("stub", Values.VModStub(name("stub"))),
)


def run(e):
    return Eval.run_expr(SIGMA, 50, RHO, e)


def flt(num, den):
    return Syntax.ExprLiteral(Syntax.LitFloat(num / den))


def prim(f, *args):
    return call(var(f), list(args))


def test_eval_call_prim_len():
    assert run(prim("len", lit(1))) == aborts(Values.TypeError_())
    assert run(prim("len")) == aborts(Values.TypeError_())


def test_eval_call_prim_round():
    """A Boolean or a second argument is excluded"""
    assert run(prim("round", Syntax.ExprLiteral(Syntax.LitBool(True)))) == aborts(Values.Excluded())
    assert run(prim("round", flt(5, 2), lit(1))) == aborts(Values.Excluded())
    assert run(prim("round", Syntax.ExprList([]))) == aborts(Values.TypeError_())


def test_eval_call_prim_exit():
    assert run(prim("exit")) == aborts(Values.Excluded())
    assert run(prim("exit", flt(1, 2))) == aborts(Values.Excluded())
    assert run(prim("exit", lit(1), lit(2))) == aborts(Values.TypeError_())


def test_eval_call_nonfun_opaque():
    """int(1): an opaque value is neither closure, primitive nor class"""
    assert run(prim("int", lit(1))) == aborts(Values.TypeError_())


def attr(e, x):
    return Syntax.ExprAttribute(e, chars(x))


def test_eval_attr_module_missing():
    assert run(attr(var("m"), "b")) == aborts(Values.AttributeError_())


def test_eval_attr_nonobject_stub():
    """A module stub is neither a loaded module nor an object"""
    assert run(attr(var("stub"), "a")) == aborts(Values.Excluded())


def match_box(*q):
    """match Box(1, 2): case q(a, b): r = 1 | case _: r = 0"""
    head = name(*q)
    p = Syntax.PatConstr(head, ([Syntax.PatVar(chars("a")), Syntax.PatVar(chars("b"))], []))
    assign = lambda n: Syntax.StmtAssign(chars("r"), Option.None_(), lit(n))
    s = Syntax.StmtMatch(
        call(var("Box"), [lit(1), lit(2)]), [(p, assign(1)), (Syntax.PatWildcard(), assign(0))]
    )
    match Eval.run_stmt(SIGMA, 50, RHO, s):
        case Eval.Done(([], Values.Assigns(delta))):
            return Finite_Map.fmlookup(EQ_VAR, delta)(chars("r"))
        case o:
            return o


def test_eval_match_qualified_head():
    """A missing attribute of a module, a stub, or a value which is not a module"""
    assert match_box("m", "C") == Eval.Done(aborts_o(Values.AttributeError_()))
    assert match_box("stub", "Box") == Eval.Done(aborts_o(Values.AttributeError_()))
    assert match_box("m", "a", "b") == Eval.Done(aborts_o(Values.AttributeError_()))


def test_eval_match_opaque_head():
    """int(...) is excluded, as Python matches it by an instance test; typing.Callable is not a class"""
    assert match_box("int") == Eval.Done(aborts_o(Values.Excluded()))
    assert match_box("Callable") == Eval.Done(aborts_o(Values.TypeError_()))

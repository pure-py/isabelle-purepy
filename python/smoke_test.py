"""Test of generated type checker on small programs; TODO: replace with full conformance test"""

import Eval
import Finite_Map
import List
import Option
import Semantics
import String
import Syntax
import Typing


def chars(s):
    """Isabelle string: list of characters, each as eight bits, least significant first"""
    return [String.Char(*(((ord(c) >> i) & 1) == 1 for i in range(8))) for c in s]


def lit(n):
    return Syntax.ExprLiteral(Syntax.LitInt(n))


def var(x):
    return Syntax.ExprVar(chars(x))


def lookup(m, x):
    return Finite_Map.fmlookup(List.equal_list(String.equal_char()), m)(chars(x))


def ret(e):
    return Syntax.StmtReturn(Option.Some(e))


predef = Finite_Map.fmap_of_list([(chars(x), Typing.PredefName()) for x in ["int", "str"]])


def annotated_int(e):
    return Syntax.StmtAssign(chars("x"), Option.Some(Syntax.TyExprPrim(Syntax.int())), e)


def test_assign_typed():
    s = annotated_int(Syntax.ExprBinOp(Syntax.BOpAdd(), lit(1), lit(2)))
    match Typing.check_stmt(predef, Option.Nonea(), s):
        case Option.Some(Typing.Assigns_R(delta)):
            assert lookup(delta, "x") == Option.Some(Typing.Ty(Syntax.TyPrim(Syntax.int())))
        case r:
            raise AssertionError(r)


def test_if_merge():
    s = Syntax.StmtIf(Syntax.ExprLiteral(Syntax.LitBool(True)), annotated_int(lit(1)), [], Option.Nonea())
    match Typing.check_stmt(predef, Option.Nonea(), s):
        case Option.Some(Typing.Assigns_R(delta)):
            assert lookup(delta, "x") == Option.Some(Typing.PU(Syntax.TyPrim(Syntax.int())))
        case r:
            raise AssertionError(r)


def test_assign_ill_typed():
    s = annotated_int(Syntax.ExprLiteral(Syntax.LitString(chars("a"))))
    assert Typing.check_stmt(predef, Option.Nonea(), s) == Option.Nonea()


def test_binop_typed():
    float_ty = Syntax.TyPrim(Syntax.float())
    cxt = Finite_Map.fmap_of_list([(chars("y"), Typing.Ty(float_ty))])
    s = ret(Syntax.ExprBinOp(Syntax.BOpAdd(), lit(1), var("y")))
    assert Typing.check_stmt(cxt, Option.Some(float_ty), s) == Option.Some(Typing.Returns_R())
    assert Typing.check_stmt(cxt, Option.Some(Syntax.TyPrim(Syntax.int())), s) == Option.Nonea()


int_ty = Syntax.TyExprPrim(Syntax.int())


def call(f, *args):
    return Syntax.ExprCall(var(f), (list(args), []))


def seq(s, *ss):
    return Syntax.StmtSeq(s, seq(*ss)) if ss else s


def if_else(e, s, s_else):
    return Syntax.StmtIf(e, s, [], Option.Some(s_else))


def defs(*ds):
    """Environment of a mutual region of definitions, each a (name, parameter, body) triple of one int parameter"""
    fs = [Syntax.Def(chars(f), [], [(chars(x), int_ty)], int_ty, s) for f, x, s in ds]
    closures = [Semantics.VDefClosure(Finite_Map.fmempty, fs, i) for i in range(len(fs))]
    return Finite_Map.fmap_of_list([(chars(f), v) for (f, _, _), v in zip(ds, closures)])


def int_val(n):
    return Eval.Done(Semantics.Val(Semantics.VLit(Syntax.LitInt(n))))


def test_eval_recursive_def():
    n = var("n")
    body = seq(
        Syntax.StmtDeclare(chars("r"), int_ty),
        if_else(Syntax.ExprBinOp(Syntax.BOpGt(), n, lit(0)),
                Syntax.StmtAssign(chars("r"), Option.Nonea(),
                                  Syntax.ExprBinOp(Syntax.BOpMul(), n,
                                                   call("fact", Syntax.ExprBinOp(Syntax.BOpSub(), n, lit(1))))),
                Syntax.StmtAssign(chars("r"), Option.Nonea(), lit(1))),
        ret(var("r")))
    assert Eval.eval_expr(200, defs(("fact", "n", body)), call("fact", lit(5))) == int_val(120)


def test_eval_mutual_recursion():
    def body(base, other):
        n = var("n")
        return if_else(Syntax.ExprBinOp(Syntax.BOpEq(), n, lit(0)),
                       ret(Syntax.ExprLiteral(Syntax.LitBool(base))),
                       ret(call(other, Syntax.ExprBinOp(Syntax.BOpSub(), n, lit(1)))))
    rho = defs(("even", "n", body(True, "odd")), ("odd", "n", body(False, "even")))
    true = Eval.Done(Semantics.Val(Semantics.VLit(Syntax.LitBool(True))))
    assert Eval.eval_expr(200, rho, call("even", lit(10))) == true
    assert Eval.eval_expr(200, rho, call("odd", lit(7))) == true
    assert Eval.eval_expr(10, rho, call("even", lit(10))) == Eval.OutOfFuel()


def test_eval_unbound_local():
    body = seq(Syntax.StmtExpr(var("r")), Syntax.StmtAssign(chars("r"), Option.Nonea(), lit(1)))
    result = Eval.eval_expr(50, defs(("g", "n", body)), call("g", lit(0)))
    assert result == Eval.Done(Semantics.Aborts(Semantics.NameError()))


def test_eval_nonbool_condition():
    body = Syntax.StmtIf(lit(1), Syntax.StmtPass(), [], Option.Nonea())
    result = Eval.eval_expr(50, defs(("g", "n", body)), call("g", lit(0)))
    assert result == Eval.Done(Semantics.Aborts(Semantics.Excluded()))


if __name__ == "__main__":
    tests = [f for name, f in sorted(globals().items()) if name.startswith("test_")]
    for test in tests:
        test()
    print(f"{len(tests)} tests passed")

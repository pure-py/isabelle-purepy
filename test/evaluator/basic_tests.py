"""Mutual recursion running out of fuel"""

from purepy.generated import Eval, Finite_Map, Option, Syntax, Values


def chars(s):
    """Identifier or string: a Python str"""
    return s


def lit(n):
    return Syntax.ExprLiteral(Syntax.LitInt(n))


def var(x):
    return Syntax.ExprVar(chars(x))


def ret(e):
    return Syntax.StmtReturn(Option.Some(e))


int_ty = Syntax.TyExprPrim(Syntax.int_())


def call(f, *args):
    return Syntax.ExprCall(var(f), (list(args), []))


def if_else(e, s, s_else):
    return Syntax.StmtIf(e, s, [], Option.Some(s_else))


def defs(*ds):
    """Environment of a mutual region of definitions, each a (name, parameter, body) triple of one int parameter"""
    fs = [Syntax.Def(chars(f), [], [(chars(x), int_ty)], int_ty, s) for f, x, s in ds]
    closures = [Values.VDefClosure(Finite_Map.fmempty, fs, i) for i in range(len(fs))]
    return Finite_Map.fmap_of_list([(chars(f), v) for (f, _, _), v in zip(ds, closures)])


def test_eval_mutual_recursion_fuel():
    """even(10) by mutual recursion runs out of fuel 10"""

    def body(base, other):
        n = var("n")
        return if_else(
            Syntax.ExprBinOp(Syntax.BOpEq(), n, lit(0)),
            ret(Syntax.ExprLiteral(Syntax.LitBool(base))),
            ret(call(other, Syntax.ExprBinOp(Syntax.BOpSub(), n, lit(1)))),
        )

    rho = defs(("even", "n", body(True, "odd")), ("odd", "n", body(False, "even")))
    assert Eval.run_expr(Finite_Map.fmempty, 10, rho, call("even", lit(10))) == Eval.OutOfFuel()

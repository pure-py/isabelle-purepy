"""Test of generated type checker on small programs; TODO: replace with full conformance test"""

import Finite_Map
import List
import Option
import String
import Syntax
import Typing


def lit(n):
    return Syntax.ExprLiteral(Syntax.LitInt(n))


def var(x):
    return Syntax.ExprVar(list(x))


def lookup(m, x):
    return Finite_Map.fmlookup(List.equal_list(String.equal_char()), m)(list(x))


def ret(e):
    return Syntax.StmtReturn(Option.Some(e))


predef = Finite_Map.fmap_of_list([(list(x), Typing.PredefName()) for x in ["int", "str"]])


def annotated_int(e):
    return Syntax.StmtAssign(list("x"), Option.Some(Syntax.TyExprPrim(Syntax.int_())), e)


def test_assign_typed():
    s = annotated_int(Syntax.ExprBinOp(Syntax.BOpAdd(), lit(1), lit(2)))
    match Typing.check_stmt(predef, Option.None_(), s):
        case Option.Some(Typing.Assigns_R(delta)):
            assert lookup(delta, "x") == Option.Some(Typing.Ty(Syntax.TyPrim(Syntax.int_())))
        case r:
            raise AssertionError(r)


def test_if_merge():
    s = Syntax.StmtIf(Syntax.ExprLiteral(Syntax.LitBool(True)), annotated_int(lit(1)), [], Option.None_())
    match Typing.check_stmt(predef, Option.None_(), s):
        case Option.Some(Typing.Assigns_R(delta)):
            assert lookup(delta, "x") == Option.Some(Typing.PU(Syntax.TyPrim(Syntax.int_())))
        case r:
            raise AssertionError(r)


def test_assign_ill_typed():
    s = annotated_int(Syntax.ExprLiteral(Syntax.LitString(list("a"))))
    assert Typing.check_stmt(predef, Option.None_(), s) == Option.None_()


def test_binop_typed():
    float_ty = Syntax.TyPrim(Syntax.float_())
    cxt = Finite_Map.fmap_of_list([(list("y"), Typing.Ty(float_ty))])
    s = ret(Syntax.ExprBinOp(Syntax.BOpAdd(), lit(1), var("y")))
    assert Typing.check_stmt(cxt, Option.Some(float_ty), s) == Option.Some(Typing.Returns_R())
    assert Typing.check_stmt(cxt, Option.Some(Syntax.TyPrim(Syntax.int_())), s) == Option.None_()


if __name__ == "__main__":
    tests = [f for name, f in sorted(globals().items()) if name.startswith("test_")]
    for test in tests:
        test()
    print(f"{len(tests)} tests passed")

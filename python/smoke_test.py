"""Test of the generated type checker on small programs; TODO: replace with full conformance test"""

import Finite_Map
import List
import Option
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
    match Typing.stmt_ty(predef, Option.Nonea(), s):
        case Option.Some(Typing.Assigns_R(delta)):
            assert lookup(delta, "x") == Option.Some(Typing.Ty(Syntax.TyPrim(Syntax.int())))
        case r:
            raise AssertionError(r)


def test_if_merge():
    s = Syntax.StmtIf(Syntax.ExprLiteral(Syntax.LitBool(True)), annotated_int(lit(1)), [], Option.Nonea())
    match Typing.stmt_ty(predef, Option.Nonea(), s):
        case Option.Some(Typing.Assigns_R(delta)):
            assert lookup(delta, "x") == Option.Some(Typing.PU(Syntax.TyPrim(Syntax.int())))
        case r:
            raise AssertionError(r)


def test_assign_ill_typed():
    s = annotated_int(Syntax.ExprLiteral(Syntax.LitString(chars("a"))))
    assert Typing.stmt_ty(predef, Option.Nonea(), s) == Option.Nonea()


def test_binop_typed():
    float_ty = Syntax.TyPrim(Syntax.float())
    cxt = Finite_Map.fmap_of_list([(chars("y"), Typing.Ty(float_ty))])
    s = ret(Syntax.ExprBinOp(Syntax.BOpAdd(), lit(1), var("y")))
    assert Typing.stmt_ty(cxt, Option.Some(float_ty), s) == Option.Some(Typing.Returns_R())
    assert Typing.stmt_ty(cxt, Option.Some(Syntax.TyPrim(Syntax.int())), s) == Option.Nonea()


if __name__ == "__main__":
    tests = [f for name, f in sorted(globals().items()) if name.startswith("test_")]
    for test in tests:
        test()
    print(f"{len(tests)} tests passed")

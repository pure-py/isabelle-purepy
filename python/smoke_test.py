"""Run the generated interpreter and type checker on small programs."""

import sys
from pathlib import Path

# Compiled evaluation judgement recurses deeply
sys.setrecursionlimit(20000)
sys.path.insert(0, str(Path(__file__).parent / "python_out" / "isabelle-purepy-python.Codegen" / "code"))

import Executable  # noqa: E402
import Finite_Map  # noqa: E402
import List  # noqa: E402
import Option  # noqa: E402
import Semantics  # noqa: E402
import String  # noqa: E402
import Syntax  # noqa: E402
import Typing  # noqa: E402


def chars(s):
    """Isabelle string: list of characters, each as eight bits, least significant first"""
    return [String.Char(*(((ord(c) >> i) & 1) == 1 for i in range(8))) for c in s]


def lit(n):
    return Syntax.ExprLiteral(Syntax.LitInt(n))


def var(x):
    return Syntax.ExprVar(chars(x))


def call(f, args):
    return Syntax.ExprCall(var(f), (args, []))


def lookup(m, x):
    return Finite_Map.fmlookup(List.equal_list(String.equal_char()), m)(chars(x))


def int_val(n):
    return Semantics.VLit(Syntax.LitInt(n))


def ret(e):
    return Syntax.StmtReturn(Option.Some(e))


empty = Finite_Map.fmempty


def test_binop():
    s = ret(Syntax.ExprBinOp(Syntax.BOpAdd(), lit(10), lit(20)))
    assert Executable.stmt_outcome(empty, s) == Semantics.Returns(int_val(30))


def test_lambda():
    body = Syntax.ExprBinOp(Syntax.BOpAdd(), var("x"), lit(1))
    s = ret(Syntax.ExprCall(Syntax.ExprLambda([chars("x")], body), ([lit(2)], [])))
    assert Executable.stmt_outcome(empty, s) == Semantics.Returns(int_val(3))


def test_zero_division():
    s = ret(Syntax.ExprBinOp(Syntax.BOpFloorDiv(), lit(1), lit(0)))
    assert Executable.stmt_outcome(empty, s) == Semantics.Aborts_o(Semantics.ZeroDivisionError())


def test_recursive_def():
    n = var("n")
    int_ty = Syntax.TyExprPrim(Syntax.int())
    body = Syntax.StmtSeq(
        Syntax.StmtIf(Syntax.ExprBinOp(Syntax.BOpEq(), n, lit(0)), ret(lit(1)), [],
                      Option.Nonea()),
        ret(Syntax.ExprBinOp(Syntax.BOpMul(), n, call("fact", [Syntax.ExprBinOp(Syntax.BOpSub(), n, lit(1))]))))
    fact = Syntax.Def(chars("fact"), [], [(chars("n"), int_ty)], int_ty, body)
    s = Syntax.StmtSeq(Syntax.StmtMutualRegion([fact]), ret(call("fact", [lit(2)])))
    assert Executable.stmt_outcome(empty, s) == Semantics.Returns(int_val(2))


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

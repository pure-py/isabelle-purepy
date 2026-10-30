"""Constructor calls and type arguments, against the generated evaluator"""

from basic_tests import chars, lit, var

from purepy.generated import (
    Contexts,
    Eval,
    Finite_Map,
    List,
    Option,
    Product_Type,
    Semantics,
    Strings,
    Syntax,
)

EQ_NAME = Product_Type.equal_prod(Strings.equal_var(), List.equal_list(Strings.equal_var()))
EQ_VAR = Strings.equal_var()
BOX = (chars("m"), [chars("Box")])
# The context of the class declaration: int is predefined
GAMMA = Finite_Map.fmupd(EQ_VAR, chars("int"), Contexts.PredefName(), Finite_Map.fmempty)
# @dataclass class Box: x: int; y: int
SIGMA = Finite_Map.fmupd(
    EQ_NAME,
    BOX,
    Contexts.ClassDef(
        GAMMA,
        (chars("m"), []),
        [
            Syntax.Dataclass(
                chars("Box"),
                [],
                Option.None_(),
                [
                    (chars("x"), Syntax.TyExprPrim(Syntax.int_())),
                    (chars("y"), Syntax.TyExprPrim(Syntax.int_())),
                ],
            )
        ],
        0,
    ),
    Finite_Map.fmempty,
)
RHO = Finite_Map.fmupd(EQ_VAR, chars("Box"), Semantics.VClass(BOX), Finite_Map.fmempty)


def run(e):
    return Eval.run_expr(SIGMA, 50, RHO, e)


def call(f, args, kws=()):
    return Syntax.ExprCall(f, (list(args), [(chars(y), e) for y, e in kws]))


def box(x, y):
    return Eval.Done(
        Semantics.Val(
            Semantics.VObject(
                BOX,
                [
                    (chars("x"), Semantics.VLit(Syntax.LitInt(x))),
                    (chars("y"), Semantics.VLit(Syntax.LitInt(y))),
                ],
            )
        )
    )


def aborts(k):
    return Eval.Done(Semantics.Aborts(k))


def test_eval_constr_positional():
    assert run(call(var("Box"), [lit(1), lit(2)])) == box(1, 2)


def test_eval_constr_keywords():
    assert run(call(var("Box"), [lit(1)], [("y", lit(2))])) == box(1, 2)
    assert run(call(var("Box"), [], [("y", lit(2)), ("x", lit(1))])) == box(1, 2)


def test_eval_constr_type_args():
    """Box[int](1, 2): the type argument is not evaluated, though int is unbound"""
    assert run(call(Syntax.ExprSubscript(var("Box"), var("int")), [lit(1), lit(2)])) == box(1, 2)


def test_eval_class_type_args():
    assert run(Syntax.ExprSubscript(var("Box"), var("int"))) == Eval.Done(
        Semantics.Val(Semantics.VClass(BOX))
    )


def test_eval_constr_fail():
    div0 = Syntax.ExprBinOp(Syntax.BOpFloorDiv(), lit(1), lit(0))
    assert run(call(var("Box"), [lit(1), div0])) == aborts(Semantics.ZeroDivisionError_())


def test_eval_call_unbound_callee():
    """f(1 // 0) with f unbound aborts with NameError, the callee being evaluated first"""
    div0 = Syntax.ExprBinOp(Syntax.BOpFloorDiv(), lit(1), lit(0))
    assert run(call(var("f"), [div0])) == aborts(Semantics.NameError_())
    assert run(call(var("f"), [], [("x", div0)])) == aborts(Semantics.NameError_())


def test_eval_constr_arity():
    """Box(1), Box(1, 2, 3), Box(1, x=2) and Box(1, z=2) have no field map and abort with TypeError"""
    assert run(call(var("Box"), [lit(1)])) == aborts(Semantics.TypeError_())
    assert run(call(var("Box"), [lit(1), lit(2), lit(3)])) == aborts(Semantics.TypeError_())
    assert run(call(var("Box"), [lit(1)], [("x", lit(2))])) == aborts(Semantics.TypeError_())
    assert run(call(var("Box"), [lit(1)], [("z", lit(2))])) == aborts(Semantics.TypeError_())

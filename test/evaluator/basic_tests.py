"""Evaluation of small programs by the generated evaluator: definitions, conditions, dictionaries, subscripts,
patterns and comprehensions"""

from purepy.generated import Eval, Finite_Map, Option, Semantics, Strings, Syntax


def chars(s):
    """Identifier or string: a Python str"""
    return s


def lit(n):
    return Syntax.ExprLiteral(Syntax.LitInt(n))


def var(x):
    return Syntax.ExprVar(chars(x))


def lookup(m, x):
    return Finite_Map.fmlookup(Strings.equal_var(), m)(chars(x))


def ret(e):
    return Syntax.StmtReturn(Option.Some(e))


int_ty = Syntax.TyExprPrim(Syntax.int_())


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
        if_else(
            Syntax.ExprBinOp(Syntax.BOpGt(), n, lit(0)),
            Syntax.StmtAssign(
                chars("r"),
                Option.None_(),
                Syntax.ExprBinOp(
                    Syntax.BOpMul(), n, call("fact", Syntax.ExprBinOp(Syntax.BOpSub(), n, lit(1)))
                ),
            ),
            Syntax.StmtAssign(chars("r"), Option.None_(), lit(1)),
        ),
        ret(var("r")),
    )
    assert Eval.run_expr(
        Finite_Map.fmempty, 200, defs(("fact", "n", body)), call("fact", lit(5))
    ) == int_val(120)


def test_eval_mutual_recursion():
    def body(base, other):
        n = var("n")
        return if_else(
            Syntax.ExprBinOp(Syntax.BOpEq(), n, lit(0)),
            ret(Syntax.ExprLiteral(Syntax.LitBool(base))),
            ret(call(other, Syntax.ExprBinOp(Syntax.BOpSub(), n, lit(1)))),
        )

    rho = defs(("even", "n", body(True, "odd")), ("odd", "n", body(False, "even")))
    true = Eval.Done(Semantics.Val(Semantics.VLit(Syntax.LitBool(True))))
    assert Eval.run_expr(Finite_Map.fmempty, 200, rho, call("even", lit(10))) == true
    assert Eval.run_expr(Finite_Map.fmempty, 200, rho, call("odd", lit(7))) == true
    assert Eval.run_expr(Finite_Map.fmempty, 10, rho, call("even", lit(10))) == Eval.OutOfFuel()


def test_eval_unbound_local():
    body = seq(Syntax.StmtExpr(var("r")), Syntax.StmtAssign(chars("r"), Option.None_(), lit(1)))
    result = Eval.run_expr(Finite_Map.fmempty, 50, defs(("g", "n", body)), call("g", lit(0)))
    assert result == Eval.Done(Semantics.Aborts(Semantics.NameError_()))


def test_eval_nonbool_condition():
    body = Syntax.StmtIf(lit(1), Syntax.StmtPass(), [], Option.None_())
    result = Eval.run_expr(Finite_Map.fmempty, 50, defs(("g", "n", body)), call("g", lit(0)))
    assert result == Eval.Done(Semantics.Aborts(Semantics.Excluded()))


def string(w):
    return Syntax.ExprLiteral(Syntax.LitString(chars(w)))


def evaluate(e):
    return Eval.run_expr(Finite_Map.fmempty, 50, Finite_Map.fmempty, e)


def val(v):
    return Eval.Done(Semantics.Val(v))


def aborts(kappa):
    return Eval.Done(Semantics.Aborts(kappa))


def test_eval_dict():
    d = Syntax.ExprDict([(string("a"), lit(1)), (string("b"), lit(2)), (string("a"), lit(3))])
    entries = [
        (chars("a"), Semantics.VLit(Syntax.LitInt(3))),
        (chars("b"), Semantics.VLit(Syntax.LitInt(2))),
    ]
    assert evaluate(d) == val(Semantics.VDict(entries))
    assert evaluate(Syntax.ExprSubscript(d, string("b"))) == int_val(2)
    assert evaluate(Syntax.ExprSubscript(d, string("c"))) == aborts(Semantics.KeyError_())
    assert evaluate(Syntax.ExprSubscript(d, lit(0))) == aborts(Semantics.Excluded())
    assert evaluate(Syntax.ExprDict([(lit(1), lit(2))])) == aborts(Semantics.Excluded())
    true = val(Semantics.VLit(Syntax.LitBool(True)))
    assert evaluate(Syntax.ExprBinOp(Syntax.BOpIn(), string("a"), d)) == true
    swapped = Syntax.ExprDict([(string("b"), lit(2)), (string("a"), lit(3))])
    assert evaluate(Syntax.ExprBinOp(Syntax.BOpEq(), d, swapped)) == true


def test_eval_subscript():
    xs = Syntax.ExprList([lit(10), lit(20), lit(30)])
    assert evaluate(Syntax.ExprSubscript(xs, lit(1))) == int_val(20)
    assert evaluate(Syntax.ExprSubscript(xs, Syntax.ExprUnOp(Syntax.UOpNeg(), lit(1)))) == int_val(
        30
    )
    assert evaluate(Syntax.ExprSubscript(xs, lit(3))) == aborts(Semantics.IndexError_())
    assert evaluate(Syntax.ExprSubscript(xs, Syntax.ExprLiteral(Syntax.LitBool(True)))) == aborts(
        Semantics.Excluded()
    )
    c = val(Semantics.VLit(Syntax.LitString(chars("b"))))
    assert evaluate(Syntax.ExprSubscript(string("abc"), lit(1))) == c
    assert evaluate(Syntax.ExprSubscript(lit(5), lit(0))) == aborts(Semantics.TypeError_())


def pvar(x):
    return Syntax.PatVar(chars(x))


def plit(n):
    return Syntax.PatLiteral(Syntax.LitInt(n))


def call_match(cases, arg):
    """Call of a function of parameter n whose body is a match on n"""
    body = Syntax.StmtMatch(var("n"), cases)
    return Eval.run_expr(Finite_Map.fmempty, 50, defs(("g", "n", body)), call("g", arg))


def test_eval_match_sequences():
    add = ret(Syntax.ExprBinOp(Syntax.BOpAdd(), var("x"), var("y")))
    cases = [(Syntax.PatList([pvar("x"), pvar("y")]), add), (Syntax.PatWildcard(), ret(lit(0)))]
    assert call_match(cases, Syntax.ExprList([lit(3), lit(4)])) == int_val(7)
    assert call_match(cases, Syntax.ExprList([lit(3)])) == int_val(0)
    assert call_match(cases, Syntax.ExprTuple([lit(3), lit(4)])) == aborts(Semantics.Excluded())
    as_x = [
        (Syntax.PatAs(Syntax.PatList([plit(1), Syntax.PatWildcard()]), chars("x")), ret(var("x")))
    ]
    pair = Syntax.ExprList([lit(1), lit(2)])
    assert call_match(as_x, pair) == evaluate(pair)


def test_eval_match_literals():
    cases = [(Syntax.PatLiteral(Syntax.LitBool(True)), ret(lit(1))), (plit(1), ret(lit(2)))]
    assert call_match(cases, lit(1)) == int_val(2)
    assert call_match(cases, Syntax.ExprLiteral(Syntax.LitBool(True))) == int_val(1)
    none = val(Semantics.VLit(Syntax.LitNone()))
    assert call_match(cases, lit(5)) == none


def test_eval_match_dict():
    cases = [
        (Syntax.PatDict([(chars("a"), pvar("x"))]), ret(var("x"))),
        (Syntax.PatWildcard(), ret(lit(0))),
    ]
    assert call_match(
        cases, Syntax.ExprDict([(string("a"), lit(1)), (string("b"), lit(2))])
    ) == int_val(1)
    assert call_match(cases, Syntax.ExprDict([(string("b"), lit(2))])) == int_val(0)


def test_eval_match_constructor_head():
    def constr(*q):
        return [(Syntax.PatConstr((chars(q[0]), [chars(x) for x in q[1:]]), ([], [])), ret(lit(1)))]

    assert call_match(constr("C"), lit(0)) == aborts(Semantics.NameError_())
    assert call_match(constr("n"), lit(0)) == aborts(Semantics.TypeError_())
    assert call_match(constr("n", "C"), lit(0)) == aborts(Semantics.AttributeError_())


def gen(x, e):
    return Syntax.Generator(chars(x), e)


def ints(*ns):
    return Syntax.ExprList([lit(n) for n in ns])


def int_list(*ns):
    return val(Semantics.VList([Semantics.VLit(Syntax.LitInt(n)) for n in ns]))


def test_eval_list_comprehension():
    double = Syntax.ExprBinOp(Syntax.BOpMul(), var("x"), lit(2))
    assert evaluate(Syntax.ExprListComp(double, [gen("x", ints(1, 2, 3))])) == int_list(2, 4, 6)
    big = Syntax.Guard(Syntax.ExprBinOp(Syntax.BOpGt(), var("x"), lit(2)))
    assert evaluate(Syntax.ExprListComp(var("x"), [gen("x", ints(1, 2, 3, 4)), big])) == int_list(
        3, 4
    )
    pairs = Syntax.ExprListComp(
        Syntax.ExprTuple([var("x"), var("y")]), [gen("x", ints(1, 2)), gen("y", string("ab"))]
    )
    expected = [
        Semantics.VTuple(
            [Semantics.VLit(Syntax.LitInt(x)), Semantics.VLit(Syntax.LitString(chars(y)))]
        )
        for x in [1, 2]
        for y in "ab"
    ]
    assert evaluate(pairs) == val(Semantics.VList(expected))
    keys = Syntax.ExprListComp(
        var("k"), [gen("k", Syntax.ExprDict([(string("a"), lit(1)), (string("b"), lit(2))]))]
    )
    assert evaluate(keys) == val(
        Semantics.VList([Semantics.VLit(Syntax.LitString(chars(k))) for k in "ab"])
    )


def test_eval_dict_comprehension():
    d = Syntax.ExprDictComp(var("k"), lit(0), [gen("k", string("aba"))])
    entries = [(chars(k), Semantics.VLit(Syntax.LitInt(0))) for k in "ab"]
    assert evaluate(d) == val(Semantics.VDict(entries))
    assert evaluate(Syntax.ExprDictComp(var("x"), lit(0), [gen("x", ints(1))])) == aborts(
        Semantics.Excluded()
    )


def test_eval_comprehension_aborts():
    assert evaluate(Syntax.ExprListComp(var("x"), [gen("x", lit(5))])) == aborts(
        Semantics.TypeError_()
    )
    assert evaluate(
        Syntax.ExprListComp(var("x"), [gen("x", ints(1)), Syntax.Guard(lit(1))])
    ) == aborts(Semantics.Excluded())
    inverse = Syntax.ExprBinOp(Syntax.BOpFloorDiv(), lit(1), var("x"))
    assert evaluate(Syntax.ExprListComp(inverse, [gen("x", ints(1, 0))])) == aborts(
        Semantics.ZeroDivisionError_()
    )


if __name__ == "__main__":
    tests = [f for name, f in sorted(globals().items()) if name.startswith("test_")]
    for test in tests:
        test()
    print(f"{len(tests)} tests passed")

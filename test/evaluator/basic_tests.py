"""Definitions, conditions, dictionaries, subscripts, patterns and comprehensions, at the aborting cases which
typing rules out, and at the fuel"""

from purepy.generated import Eval, Finite_Map, Option, Strings, Syntax, Values
from purepy.syntax import parse_name


def chars(s):
    """Identifier or string: a Python str"""
    return s


def name(*xs):
    """Name of the variables xs, as the parser gives it"""
    return parse_name(".".join(xs))


def aborts_o(k):
    """Outcome of an abort, printing nothing"""
    return ([], Values.Aborts_omega(k))


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


def test_eval_unbound_local():
    body = seq(Syntax.StmtExpr(var("r")), Syntax.StmtAssign(chars("r"), Option.None_(), lit(1)))
    result = Eval.run_expr(Finite_Map.fmempty, 50, defs(("g", "n", body)), call("g", lit(0)))
    assert result == Eval.Done(Values.Aborts(Values.NameError_()))


def test_eval_nonbool_condition():
    body = Syntax.StmtIf(lit(1), Syntax.StmtPass(), [], Option.None_())
    result = Eval.run_expr(Finite_Map.fmempty, 50, defs(("g", "n", body)), call("g", lit(0)))
    assert result == Eval.Done(Values.Aborts(Values.Excluded()))


def string(w):
    return Syntax.ExprLiteral(Syntax.LitString(chars(w)))


def evaluate(e):
    return Eval.run_expr(Finite_Map.fmempty, 50, Finite_Map.fmempty, e)


def aborts(kappa):
    return Eval.Done(Values.Aborts(kappa))


def test_eval_dict_nonstr_key():
    """A key other than a string, in a display or a subscript"""
    d = Syntax.ExprDict([(string("a"), lit(1))])
    assert evaluate(Syntax.ExprSubscript(d, lit(0))) == aborts(Values.Excluded())
    assert evaluate(Syntax.ExprDict([(lit(1), lit(2))])) == aborts(Values.Excluded())


def test_eval_subscript():
    """A Boolean index, and a subscript of an int"""
    xs = Syntax.ExprList([lit(10), lit(20), lit(30)])
    assert evaluate(Syntax.ExprSubscript(xs, Syntax.ExprLiteral(Syntax.LitBool(True)))) == aborts(
        Values.Excluded()
    )
    assert evaluate(Syntax.ExprSubscript(lit(5), lit(0))) == aborts(Values.TypeError_())


def call_match(cases, arg):
    """Call of a function of parameter n whose body is a match on n"""
    body = Syntax.StmtMatch(var("n"), cases)
    return Eval.run_expr(Finite_Map.fmempty, 50, defs(("g", "n", body)), call("g", arg))


def test_eval_match_list_tuple():
    """A list pattern against a tuple"""
    pattern = Syntax.PatList([Syntax.PatVar(chars("x")), Syntax.PatVar(chars("y"))])
    cases = [(pattern, ret(lit(1))), (Syntax.PatWildcard(), ret(lit(0)))]
    assert call_match(cases, Syntax.ExprTuple([lit(3), lit(4)])) == aborts(Values.Excluded())


def test_eval_match_constructor_head():
    """An unbound head, a head that is not a class, and a missing attribute of a head"""

    def constr(*q):
        return [(Syntax.PatConstr(name(*q), ([], [])), ret(lit(1)))]

    assert call_match(constr("C"), lit(0)) == aborts(Values.NameError_())
    assert call_match(constr("n"), lit(0)) == aborts(Values.TypeError_())
    assert call_match(constr("n", "C"), lit(0)) == aborts(Values.AttributeError_())


def gen(x, e):
    return Syntax.Generator(chars(x), e)


def ints(*ns):
    return Syntax.ExprList([lit(n) for n in ns])


def test_eval_comprehension_aborts():
    """A generator over an int, a guard that is not a Boolean, and a key that is not a string"""
    assert evaluate(Syntax.ExprListComp(var("x"), [gen("x", lit(5))])) == aborts(
        Values.TypeError_()
    )
    assert evaluate(
        Syntax.ExprListComp(var("x"), [gen("x", ints(1)), Syntax.Guard(lit(1))])
    ) == aborts(Values.Excluded())
    assert evaluate(Syntax.ExprDictComp(var("x"), lit(0), [gen("x", ints(1))])) == aborts(
        Values.Excluded()
    )

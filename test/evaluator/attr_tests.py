"""Attribute access, at the aborting cases which typing rules out"""

from basic_tests import chars, lit, var
from constr_tests import aborts, call, run

from purepy.generated import Syntax, Values


def attr(e, x):
    return Syntax.ExprAttribute(e, chars(x))


def box12():
    return call(var("Box"), [lit(1), lit(2)])


def test_eval_attr_missing():
    assert run(attr(box12(), "z")) == aborts(Values.AttributeError_())


def test_eval_attr_nonobject():
    """1.x and Box.x: neither an int nor a class is an object"""
    assert run(attr(lit(1), "x")) == aborts(Values.Excluded())
    assert run(attr(var("Box"), "x")) == aborts(Values.Excluded())


def test_eval_attr_fail():
    """Box(1).x aborts with the constructor's TypeError, and f.x with NameError"""
    assert run(attr(call(var("Box"), [lit(1)]), "x")) == aborts(Values.TypeError_())
    assert run(attr(var("f"), "x")) == aborts(Values.NameError_())

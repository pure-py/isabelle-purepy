"""Rules of the specification violated by the reasons of the generated type checker, named as the conformance
suite cites them"""

import re

from .generated import Reasons
from .syntax import Reason

PREFIX = "Rule"


def rule_name(n: object) -> str:
    """Name of rule n in the specification, its constructor's name without the prefix and in kebab case"""
    return re.sub(r"(?<!^)(?=[A-Z])", "-", type(n).__name__.removeprefix(PREFIX)).lower()


def rule_names() -> set[str]:
    return {
        rule_name(c())
        for x, c in vars(Reasons).items()
        if x.startswith(PREFIX) and isinstance(c, type)
    }


def rule(r: Reason) -> str:
    match r:
        case Reasons.Located(_, r_) | Reasons.MypyCompatibility(r_):
            return rule(r_)
        case Reasons.Violates(n, _):
            return rule_name(n)
        case _:
            raise AssertionError(f"reason violates no rule: {r}")

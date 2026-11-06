"""Rules and judgements of the specification under which the generated type checker rejects programs, named as
the conformance suite cites them"""

import re

from .generated import Reasons
from .syntax import Reason

RULE = "Rule"
JUDGEMENT = "Judgement"


def spec_name(c: object, prefix: str) -> str:
    """Name in the specification of constructor c, its name without the prefix and in kebab case"""
    return re.sub(r"(?<!^)(?=[A-Z])", "-", type(c).__name__.removeprefix(prefix)).lower()


def spec_names(prefix: str) -> set[str]:
    return {
        spec_name(c(), prefix)
        for x, c in vars(Reasons).items()
        if x.startswith(prefix) and isinstance(c, type)
    }


def citation(r: Reason) -> tuple[str | None, str | None]:
    """Judgement which selects no rule, or rule violated, by r"""
    match r:
        case Reasons.Located(_, r_) | Reasons.MypyCompatibility(r_):
            return citation(r_)
        case Reasons.Violates(n, _):
            return (None, spec_name(n, RULE))
        case Reasons.SelectsNoRule(j, _):
            return (spec_name(j, JUDGEMENT), None)
        case _:
            raise AssertionError(f"reason under no rule or judgement: {r}")

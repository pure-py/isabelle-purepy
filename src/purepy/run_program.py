"""Running a program by the generated reference interpreter, after checking it by the generated type checker"""

import pathlib
import sys
import threading
from typing import Any

from . import syntax
from .check_program import format_program_result, parse_program, translate_program
from .generated import Contexts, Eval, Option, Programs, Sum_Type, Syntax
from .reasons import IllFormed
from .translate import ill_formed

# Exit statuses of a run which does not end as Python's would
UNDEFINED = 5  # Undef or Excluded: behaviour the semantics leaves undefined or excludes
STUCK = 6  # no rule applies, which type soundness rules out
OUT_OF_FUEL = 7

DEFAULT_FUEL = 100_000


def check(M: Any) -> tuple[IllFormed | None, Any]:
    """Failure of checking the program, or the class table of the checked program"""
    match Programs.check_module(M, [], Contexts.predefined_classes, Syntax.main, Syntax.main):
        case Sum_Type.Inl((q, r)):
            return ill_formed(q, r), None
        case Sum_Type.Inr((_, sigma)):
            return None, sigma
        case result:
            raise AssertionError(f"unexpected result: {result}")


def kind(x: Any) -> str:
    return type(x).__name__.rstrip("_")


def report(kappa: Any) -> int:
    """Exit status for termination kind kappa, after writing an exception as Python would"""
    match kind(kappa):
        case "SystemExit":
            return int(kappa.a)
        case "Undef" | "Excluded":
            print(f"purepy: {kind(kappa)}", file=sys.stderr)
            return UNDEFINED
        case "AssertionError" if isinstance(kappa.a, Option.Some):
            print(f"AssertionError: {kappa.a.a}", file=sys.stderr)
            return 1
        case name:
            print(name, file=sys.stderr)
            return 1


def evaluate(sigma: Any, M: Any, fuel: int) -> int:
    match Eval.run_program(sigma, M, fuel):
        case Eval.Done(kappa):
            return report(kappa)
        case Eval.Stuck():
            print("purepy: stuck", file=sys.stderr)
            return STUCK
        case Eval.OutOfFuel():
            print("purepy: out of fuel", file=sys.stderr)
            return OUT_OF_FUEL
        case result:
            raise AssertionError(f"unexpected result: {result}")


def run_program(entry_path: pathlib.Path, fuel: int = DEFAULT_FUEL) -> int:
    """Exit status of the program at entry_path. The interpreter recurses as deeply as derivations nest, so it
    runs in a thread with a large stack."""
    try:
        M = translate_program(parse_program(entry_path))
    except syntax.Unsupported as e:
        print(format_program_result(e, entry_path))
        return e.exit_code
    failure, sigma = check(M)
    if failure is not None:
        print(format_program_result(failure, entry_path))
        return failure.exit_code
    status: list[int] = [OUT_OF_FUEL]
    sys.setrecursionlimit(10**6)
    threading.stack_size(1 << 29)
    thread = threading.Thread(target=lambda: status.__setitem__(0, evaluate(sigma, M, fuel)))
    thread.start()
    thread.join()
    return status[0]

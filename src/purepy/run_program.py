"""Running a program by the generated reference interpreter, after checking it by the generated type checker"""

import pathlib
import sys
import threading
from typing import Any

from . import syntax
from .check_program import IllFormed, exit_code, format_program_rejection, parse_program
from .generated import Contexts, Eval, Option, Programs, Sum_Type, Syntax
from .syntax import Program

# Exit statuses of a run which does not end as Python's would
UNDEFINED = 5  # Undef or Excluded: behaviour the semantics leaves undefined or excludes
STUCK = 6  # no rule applies, which type soundness rules out
OUT_OF_FUEL = 7

DEFAULT_FUEL = 100_000


def check(M: Program) -> tuple[IllFormed | None, Any]:
    """Module and reason of an ill-formed program, or the class table of the checked program"""
    match Programs.check_module(M, [], Contexts.predefined_classes, Syntax.main, Syntax.main):
        case Sum_Type.Inl((q, r)):
            return (q, r), None
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


def evaluate(sigma: Any, M: Any, argv: list[str], fuel: int) -> int:
    match Eval.run_program(sigma, M, argv, fuel):
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


def run_program(
    entry_path: pathlib.Path, args: list[str] | None = None, fuel: int = DEFAULT_FUEL
) -> int:
    """Exit status of the program at entry_path, run with command-line arguments args, so that sys.argv is the
    path followed by args. The interpreter recurses as deeply as derivations nest, so it
    runs in a thread with a large stack."""
    try:
        M = parse_program(entry_path)
    except syntax.ParserRejects as e:
        print(format_program_rejection(e, entry_path))
        return int(exit_code(e))
    rejection, sigma = check(M)
    if rejection is not None:
        print(format_program_rejection(rejection, entry_path))
        return int(exit_code(rejection))
    status: list[int] = [OUT_OF_FUEL]
    sys.setrecursionlimit(10**6)
    threading.stack_size(1 << 29)
    thread = threading.Thread(
        target=lambda: status.__setitem__(
            0, evaluate(sigma, M, [str(entry_path), *(args or [])], fuel)
        )
    )
    thread.start()
    thread.join()
    return status[0]

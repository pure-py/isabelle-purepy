"""Running a program by the generated reference interpreter, after checking it by the generated type checker"""

import pathlib
import sys
import threading
from typing import Any

from purepy_conformance import Exit

from . import syntax
from .check_program import Diagnostic, diagnostic, exit_code, format_diagnostic, parse_program
from .generated import Contexts, Eval, Option, Programs, Sum_Type, Syntax, Values
from .messages import unparse_value
from .syntax import Program

# Exit statuses of a run which doesn't end as in Python, other than undefined behaviour
STUCK = 6  # stuck run, ruled out by type soundness
OUT_OF_FUEL = 7

DEFAULT_FUEL = 100_000


def check(entry_path: pathlib.Path) -> Diagnostic | tuple[Program, Any]:
    """Diagnostic of an ill-formed program at entry_path, or the program with the class table from the type
    checker"""
    try:
        M = parse_program(entry_path)
    except syntax.ParserRejects as e:
        return diagnostic(e)
    match Programs.check_module(M, [], Contexts.predefined_classes, Syntax.main, Syntax.main):
        case Sum_Type.Inl((q, r)):
            return diagnostic(Programs.IllFormed(q, r))
        case Sum_Type.Inr((_, sigma)):
            return M, sigma
        case result:
            raise AssertionError(f"unexpected result: {result}")


def kind(x: Any) -> str:
    return type(x).__name__.rstrip("_")


def printed(v: Any) -> str:
    """String printed by Python for v"""
    match v:
        case Values.VLit(Syntax.LitString(w)):
            return str(w)
        case _:
            return unparse_value(v)


def report(kappa: Any) -> int:
    """Write termination kind kappa to standard error, except for a system exit, and return its exit status"""
    match kind(kappa):
        case "SystemExit":
            return int(kappa.a)
        case "Undef" | "Excluded":
            print(f"purepy: {kind(kappa)}", file=sys.stderr)
            return int(Exit.UNDEFINED)
        case "AssertionError" if isinstance(kappa.a, Option.Some):
            print(f"AssertionError: {kappa.a.a}", file=sys.stderr)
            return 1
        case name:
            print(name, file=sys.stderr)
            return 1


def evaluate(sigma: Any, M: Program, argv: list[str], fuel: int) -> int:
    match Eval.run_program(sigma, M, fuel, argv):
        case Eval.Done((vs, kappa)):
            for v in vs:
                print(printed(v))
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
    """Run the program at entry_path with command-line arguments args and return the exit status. The
    interpreter recurses as deeply as derivations nest, so the run gets a thread with a large stack."""
    match check(entry_path):
        case Diagnostic() as d:
            print(format_diagnostic(d, entry_path))
            return int(exit_code(d))
        case (M, sigma):
            pass
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

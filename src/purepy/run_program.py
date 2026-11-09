"""Running a program by the generated reference interpreter, after checking it by the generated type checker"""

import dataclasses
import pathlib
import sys
import threading
from typing import Any

from purepy_conformance import Exit

from .check_program import check_program, exit_code, format_diagnostic, parse_program
from .generated import Contexts, Eval, Option, Programs, Sum_Type, Syntax
from .syntax import Program

# Exit statuses of a run which does not end as Python's would, besides Exit.UNDEFINED
STUCK = 6  # no rule applies, which type soundness rules out
OUT_OF_FUEL = 7

DEFAULT_FUEL = 100_000


def class_table(M: Program) -> Any:
    """Class table of a well-formed program"""
    match Programs.check_module(M, [], Contexts.predefined_classes, Syntax.main, Syntax.main):
        case Sum_Type.Inr((_, sigma)):
            return sigma
        case result:
            raise AssertionError(f"unexpected result: {result}")


def args(x: Any) -> list[Any]:
    return [getattr(x, f.name) for f in dataclasses.fields(x)]


def kind(x: Any) -> str:
    return type(x).__name__.rstrip("_")


def qualified(q: Any) -> str:
    return ".".join(Syntax.variables(q))


def to_str(v: Any, nested: bool = False) -> str:
    """Value as Python's str writes it, or its repr inside a container"""
    match kind(v):
        case "VLit":
            (lit,) = args(v)
            match kind(lit):
                case "LitInt":
                    return str(args(lit)[0])
                case "LitFloat":
                    return repr(args(lit)[0])
                case "LitString":
                    w = args(lit)[0]
                    return repr(w) if nested else str(w)
                case "LitBool":
                    return "True" if args(lit)[0] else "False"
                case _:
                    return "None"
        case "VList":
            return "[" + ", ".join(to_str(u, True) for u in args(v)[0]) + "]"
        case "VTuple":
            us = args(v)[0]
            return (
                "(" + ", ".join(to_str(u, True) for u in us) + ("," if len(us) == 1 else "") + ")"
            )
        case "VDict":
            return "{" + ", ".join(f"{w!r}: {to_str(u, True)}" for w, u in args(v)[0]) + "}"
        case "VObject":
            c, fields = args(v)
            x = Syntax.variables(c)[-1]
            return f"{x}(" + ", ".join(f"{y}={to_str(u, True)}" for y, u in fields) + ")"
        case "VClass":
            return f"<class '{qualified(args(v)[0])}'>"
        case "VPrim":
            return f"<built-in function {kind(args(v)[0])[4:].lower()}>"
        case "VModStub" | "VModLoaded":
            return f"<module '{qualified(args(v)[0])}'>"
        case k:
            return f"<{k}>"


def report(kappa: Any) -> int:
    """Exit status for termination kind kappa, after writing an exception as Python would"""
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
                print(to_str(v))
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
    d = check_program(entry_path)
    if d is not None:
        print(format_diagnostic(d, entry_path))
        return int(exit_code(d))
    M = parse_program(entry_path)
    sigma = class_table(M)
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

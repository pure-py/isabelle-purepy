"""Build ASTs which ast.parse can't produce and check PurePy rejects them."""

import ast
import sys

from purepy.check_program import MAIN, check, program
from purepy.messages import IllFormed
from purepy.syntax import Unsupported, check_syntax_module, module_body


def expect_rejected(m: ast.Module, msg_contains: str = "") -> None:
    result: IllFormed | Unsupported | None = check_syntax_module(m)
    if result is None:
        result = check(program({MAIN: module_body(MAIN, m)}))
    if result is None:
        print("FAIL: expected rejection but got ok", file=sys.stderr)
        sys.exit(1)
    if len(msg_contains) > 0 and msg_contains not in result.msg:
        print(
            f"FAIL: expected message containing {msg_contains!r}, got {result.msg!r}",
            file=sys.stderr,
        )
        sys.exit(1)
    print(f"ok: {result.msg}")

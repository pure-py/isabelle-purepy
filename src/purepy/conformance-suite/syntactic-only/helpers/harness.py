"""Build ASTs which ast.parse can't produce and check PurePy rejects them."""

import ast
import sys

from purepy.check_program import MAIN, check, program
from purepy.messages import message
from purepy.syntax import check_syntax_module, module_body


def expect_rejected(m: ast.Module, msg_contains: str = "") -> None:
    unsupported = check_syntax_module(m)
    if unsupported is not None:
        msg = unsupported.msg
    else:
        result = check(program({MAIN: module_body(MAIN, m)}))
        if result is None:
            print("FAIL: expected rejection but got ok", file=sys.stderr)
            sys.exit(1)
        msg = message(result[1])
    if len(msg_contains) > 0 and msg_contains not in msg:
        print(f"FAIL: expected message containing {msg_contains!r}, got {msg!r}", file=sys.stderr)
        sys.exit(1)
    print(f"ok: {msg}")

"""Build ASTs which ast.parse can't produce and check PurePy rejects them."""

import ast
import sys

from purepy.check_program import MAIN, check, program
from purepy.messages import message
from purepy.syntax import ParserRejects, module_body


def expect_rejected(m: ast.Module, msg_contains: str = "") -> None:
    try:
        body = module_body(MAIN, m)
    except ParserRejects as e:
        msg = e.msg
    else:
        result = check(program({MAIN: body}))
        if result is None:
            print("FAIL: expected rejection but got ok", file=sys.stderr)
            sys.exit(1)
        msg = message(result[1])
    if len(msg_contains) > 0 and msg_contains not in msg:
        print(f"FAIL: expected message containing {msg_contains!r}, got {msg!r}", file=sys.stderr)
        sys.exit(1)
    print(f"ok: {msg}")

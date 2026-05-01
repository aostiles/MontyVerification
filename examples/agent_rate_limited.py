# call-external
"""§3.1 Rate-limited pipeline.

This example demonstrates a "no more than N tool calls per session"
invariant via a session-state value indexed by the remaining token
budget. The Python source below is just a placeholder — the actual
type-state encoding lives in the matching `.lean` file, which
defines a `RateLimited` type that *forces* the user to thread tokens
through every call.

The pattern: each tool call consumes a token; when tokens run out,
the next call won't type-check (no value of `RateLimited 0` can
produce a `RateLimited 1`). This is type-state, encoded directly
in Lean's dependent types.
"""


def trim(text: str, limit: int) -> Pure[str]:
    """Pure helper, used by the rate-limited workflow downstream."""
    return text[:limit]


# Direct test of the pure helper.
assert trim('hello world', 5) == 'hello', 'trim cuts long text'

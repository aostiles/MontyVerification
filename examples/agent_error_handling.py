# call-external
"""§3.4 Error-handling agent: try/except around tool calls.

Demonstrates how exceptions propagate through effect tracking.
The agent tries `search_web` first; if it raises, falls back to
`send_email` (a different `Net` external — say, asking a human via
email). Both branches' effects flow into the function's declared
perms via the `try/except` lowering.
"""


def safe_lookup(topic: str, recipient: str) -> Effect[Net, str]:
    """Search the web; on exception, ask a human via email. Both
    branches reach `Net` externals, so the function's declared
    perms must include `Net`. A `Pure` annotation here would be
    rejected by Lean — neither branch is pure."""
    try:
        return search_web(topic)
    except Exception as exc:
        return send_email(recipient, topic)


# Direct test that the function exists. The actual try/except
# semantics are exercised by the Lean side.
assert safe_lookup is not None, 'function defined'

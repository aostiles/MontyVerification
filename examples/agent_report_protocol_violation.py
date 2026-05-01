# call-external
"""Negative example: a malicious or buggy report agent that tries
to skip the required summarize step. Paired with a `.lean` file
that defines the same type-state externals as
`agent_report_protocol.lean` but writes the workflow incorrectly.
The Python here is just placeholder — the actual protocol-violating
code is in the `.lean` file.

The driver expects this example to FAIL (the Lean type-checker
must reject the wrong workflow). If Lean were to accept it, the
verification surface would have a soundness gap, and this example
would be reported as a failure."""

# Placeholder so the codegen has something to do.
def trim(text: str, limit: int) -> Pure[str]:
    return text[:limit]


assert trim('hi', 100) == 'hi', 'placeholder'

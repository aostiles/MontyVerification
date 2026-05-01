# call-external
"""Realistic code-mode-style agent: protocol-checked report pipeline.

This is the most interesting verification story for code-mode agents:
**ordering invariants** on tool calls. The deployer wants to enforce
"no `generate_report` call may happen unless `summarize` was called
first" — a property that's invisible to a permissions-only effect
system but trivial for a type-state model.

The Python source below is what the LLM writes. It looks like
ordinary procedural code: summarize, then generate_report, then
send_notification. The verification layer (in
`agent_report_protocol.lean`) defines TYPED versions of those
externals where each call returns a witness token, and the next
call requires that token. The CORRECT workflow type-checks; a wrong
workflow that calls `generate_report` without first calling
`summarize` is rejected by Lean's type checker — there's no value
of type `SummaryToken` to pass.

The agent is free to compose pure helpers, vary the input, run
different reports, etc. — the type system only enforces the
ordering, leaving all other creative latitude intact.
"""


def trim(text: str, limit: int) -> Pure[str]:
    """Pure helper: bounds the input length."""
    return text[:limit]


def report_pipeline(topic: str, recipient: str) -> Effect[Net, str]:
    """The agent's workflow: search for content on a topic, summarize
    it, generate a report from the summary, and notify the
    recipient. The required ordering is summarize → generate_report
    → send_notification."""
    raw = search_web(topic)
    bounded = trim(raw, 500)
    summary = summarize(bounded)
    report = generate_report(summary)
    send_notification(recipient, report)
    return report


# Pure helper assertions (no externals).
assert trim('hello world', 5) == 'hello', 'trim cuts long text'
assert trim('hi', 100) == 'hi', 'trim preserves short text'
assert trim('abcdefghij', 3) == 'abc', 'exact bound'

# call-external
"""Realistic code-mode-style agent: a research pipeline.

The pattern: an LLM is given a typed API exposing `search_web` and
`send_email` (the externals), and writes the orchestration code below
to fulfill a "research a topic and email me the results" request.
The whole program runs in a sandbox; the verification layer enforces
that

  - `truncate` declares `Pure[str]` and *actually is* pure (no
    externals reachable from its body),
  - `research_and_notify` declares `Effect[Net, str]` and reaches both
    Net externals correctly, and
  - the test assertions about the pure helper reduce to concrete
    values, so the file as a whole has a real (not vacuous) verified
    behavior.

Cloudflare's "Code Mode" proposal turns each MCP tool into a typed
SDK function that the LLM can call from code; MontyVerification's
effect annotations are the verification layer for exactly that
pattern. If the LLM-written `research_and_notify` accidentally
declared `Pure[str]` instead, Lean would reject the file at compile
time — the soundness story.
"""


def truncate(text: str, limit: int) -> Pure[str]:
    """Bounded "summarization": take a prefix of the input. Pure
    helper, no externals."""
    if len(text) > limit:
        return text[:limit]
    return text


def research_and_notify(topic: str, recipient: str) -> Effect[Net, str]:
    """The agent body. Search the web, truncate the result to keep
    it bounded, send the truncated result via email."""
    raw = search_web(topic)
    summary = truncate(raw, 200)
    send_email(recipient, summary)
    return summary


# Direct tests of the pure helper. These reduce by `decide` because
# `truncate` has no axiomatic dependencies.
assert truncate('hello world', 5) == 'hello', 'truncate cuts long text'
assert truncate('hi', 100) == 'hi', 'truncate preserves short text'
assert truncate('abcdefghij', 3) == 'abc', 'exact bound'
assert truncate('', 10) == '', 'empty input'

# call-external
"""Realistic code-mode-style agent: a multi-turn REPL session.

The setup: an LLM is running in a REPL where each "turn" is a
small program that operates on the persistent session state. The
agent (or a series of agent prompts) might:

  Turn 1: summarize an article
  Turn 2: generate a report from the summary
  Turn 3: notify a recipient about the report

Across turns, the session state must enforce the same protocol
invariant the single-turn case does: `generate_report` must come
after `summarize`, and `send_notification` must come after
`generate_report` — even when each call lives in a different
turn.

The Python source below is what the LLM-as-REPL would emit across
turns (we squash them into one file for the codegen). The
verification value is in the paired `.lean` file, which models
the session as a value of type `Session s r` whose TYPE encodes
which protocol checkpoints have been reached. Each turn's signature
takes a session in some state and produces one in a (possibly
upgraded) state. Lean's type checker enforces the order across the
whole session — there is no way to "skip" `summarize` between
turns, because turn 2's input type literally requires the
upgraded state.

The pattern is what session types / type-state are designed for.
Global mutable state would lose the ordering information; a flat
state monad would be unable to enforce the ordering at the type
level. Indexing the state by protocol checkpoints is the right
shape for verifying multi-turn LLM workflows.
"""


def trim(text: str, limit: int) -> Pure[str]:
    return text[:limit]


# Pure-helper assertions.
assert trim('hello world', 5) == 'hello', 'trim cuts long text'
assert trim('hi', 100) == 'hi', 'trim preserves short text'

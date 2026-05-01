# call-external
"""Effect inference: no `Pure[]` / `Effect[]` annotations.

Real LLM-generated Python rarely carries effect annotations. The
codegen infers each function's effect set from its body — the union
of every external it (transitively) calls. This file is the same
shape as `agent_research_pipeline.py` but with all annotations
stripped, and the matching `.lean` proves that the verification
still recovers the right effect types from the call graph.
"""


def trim(text, limit):
    if len(text) > limit:
        return text[:limit]
    return text


def fetch_one(topic):
    return search_web(topic)


def research_and_notify(topic, recipient):
    raw = fetch_one(topic)
    summary = trim(raw, 200)
    send_email(recipient, summary)
    return summary


# Pure-helper assertions reduce by computation.
assert trim('hello world', 5) == 'hello'
assert trim('hi', 100) == 'hi'

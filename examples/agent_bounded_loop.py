# call-external
"""§3.5 Bounded for-loop over a tool result.

The most common agent shape: get a list, do X with each item.
This example shows the verification reasoning: the loop is
bounded by the (already-fetched) list's length, every per-item
operation is `Net`, and the function as a whole is `Net`.
"""


def render(item: str) -> Pure[str]:
    """Pure formatting helper."""
    return '* ' + item


def fetch_and_summarize(topic: str) -> Effect[Net, str]:
    """Fetch a list of items via the network, render each one
    (pure), and concatenate. The bounded `for` loop iterates over
    the fetched list — every iteration runs `render` which is
    pure, but the initial fetch is `Net`."""
    items = search_web(topic)
    out = ''
    for item in items:
        out = out + render(item)
    return out


# Direct tests of the pure helper.
assert render('foo') == '* foo', 'render prefixes a bullet'
assert render('') == '* ', 'render handles empty input'

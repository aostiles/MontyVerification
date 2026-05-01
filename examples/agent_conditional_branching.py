# call-external
"""§3.3 Conditional branching workflow.

An agent that branches on a tool result. The pattern: search the
web, check if the result looks empty, fall back to a different
query if so. Both branches must respect the `Net` effect; the
verification proves the merged post-state has the right perms.
"""


def is_empty(s: str) -> Pure[bool]:
    """Pure check: is this result effectively empty?"""
    return len(s) == 0


def search_with_fallback(topic: str, fallback_topic: str) -> Effect[Net, str]:
    """Search for `topic`. If the result is empty, search for
    `fallback_topic` instead. Both branches reach `search_web`, so
    both reach `Net`. Lean verifies that the merged post-state has
    `{ net := true }` regardless of which branch fires."""
    primary = search_web(topic)
    if is_empty(primary):
        return search_web(fallback_topic)
    return primary


# Direct tests of the pure helper.
assert is_empty('') == True, 'empty string is empty'
assert is_empty('hi') == False, 'non-empty string is not empty'

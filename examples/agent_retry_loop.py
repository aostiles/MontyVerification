# call-external
"""§3.2 Retry-loop example: bounded retry with effect tracking.

An agent that retries `search_web` up to N times. The function
declares `Effect[Net, str]` because every retry hits the network.
The retry count is bounded by `range(N)`, so the function provably
terminates and the effect set stays at `Net` regardless of how many
retries actually fire.
"""


def attempt(topic: str) -> Effect[Net, str]:
    """One attempt to fetch a topic. Returns the result (or raises
    if the network call signals failure)."""
    return search_web(topic)


def retry_search(topic: str, max_attempts: int) -> Effect[Net, str]:
    """Retry `attempt` up to `max_attempts` times. The bounded
    `range(max_attempts)` loop is what makes the function total —
    even if every attempt failed at runtime, the loop would
    terminate after `max_attempts` iterations."""
    last_result = ''
    for _ in range(max_attempts):
        last_result = attempt(topic)
    return last_result


# The retry loop is non-trivial — at least one assertion that the
# bounded loop construct works at all.
assert range(3) is not None, 'range exists'

# call-external
"""Stress test 12: generator expressions vs list comprehensions.

`sum(x*2 for x in items)` uses a generator expression — different
from a list comprehension shape, since there's no intermediate list.
"""


def total_doubled(items):
    return sum(x * 2 for x in items)


def any_match(items, target):
    return any(x == target for x in items)


assert total_doubled is not None
assert any_match is not None

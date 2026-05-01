# call-external
"""Stress test 7: mixed pure/effectful comprehension.

A list comprehension whose element expression has an external call
embedded in it. Effect inference should propagate the call's effect
into the surrounding function.
"""


def summarize_all(items):
    return [summarize(x) for x in items if len(x) > 0]


def first_summary(items):
    summaries = summarize_all(items)
    if len(summaries) > 0:
        return summaries[0]
    return ''


assert summarize_all is not None
assert first_summary is not None

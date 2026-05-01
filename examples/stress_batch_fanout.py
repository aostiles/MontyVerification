# call-external
"""Stress test 2: batch fanout/fanin.

The most common agent shape: get a list, do something with each item,
collect results. Exercises append-style mutation, which our model
doesn't support — see what happens.
"""


def process_batch(items):
    results = []
    for item in items:
        processed = transform(item)
        results.append(processed)
    return results


def summarize_results(items):
    out = process_batch(items)
    return len(out)


assert summarize_results is not None

# call-external
"""Stress test 15: string formatting with f-strings and externals.

F-strings with effectful interpolations are a known mal-harness
case (effect leakage). This is a sound shape: the interpolations
are pure computations.
"""


def format_user(user_id, name):
    return f'user_{user_id}: {name}'


def report(items, total):
    return f'{len(items)} items, total {total}'


assert format_user is not None
assert report is not None

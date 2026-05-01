# call-external
"""Stress test 14: method chaining and fluent APIs.

The `obj.method1().method2().method3()` shape — common in builder
patterns and string manipulation.
"""


def normalize(text):
    return text.strip().lower().replace(' ', '_')


def parts_of(line):
    return line.strip().split(',')


assert normalize is not None
assert parts_of is not None

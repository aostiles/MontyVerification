"""Stress test for P1 partial fix: list mutation via .append.

The codegen now lowers `lst.append(x)` to a re-binding
`let lst := pyListAppend lst x` so the model tracks the appended
elements. This handles the most common LLM-generated mutation
shape (`lst = []; lst.append(...)`).
"""


def collect_squares(n):
    out = []
    out.append(n * n)
    out.append((n + 1) * (n + 1))
    return out


def append_then_extend(items):
    out = []
    out.append(0)
    out.extend(items)
    out.append(99)
    return out


# These assertions REDUCE in the model now, because the appended
# elements actually flow through the let-rebinding.
assert collect_squares(3) == [9, 16], 'collect_squares with n=3'
assert collect_squares(0) == [0, 1], 'collect_squares with n=0'

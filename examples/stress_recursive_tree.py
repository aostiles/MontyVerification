# call-external
"""Stress test 5: recursive tree walk.

Exercises the G3 fuel transform on a non-trivial recursion shape.
"""


def tree_size(node):
    if is_leaf(node):
        return 1
    left = tree_size(get_left(node))
    right = tree_size(get_right(node))
    return 1 + left + right


def tree_sum(node):
    if is_leaf(node):
        return get_value(node)
    return get_value(node) + tree_sum(get_left(node)) + tree_sum(get_right(node))


assert tree_size is not None
assert tree_sum is not None

# call-external
"""Stress test 9: shadowing and re-binding.

Variables that get re-bound in different scopes. The codegen should
handle Python's flat function-scope semantics correctly.
"""


def shadowing_demo(items):
    x = 1
    for x in items:
        process_item(x)
    return x  # Python: x is the LAST loop value, not the original 1


def nested_shadow(outer):
    def inner(outer):
        return outer * 2
    return inner(outer + 1)


assert shadowing_demo is not None
assert nested_shadow is not None

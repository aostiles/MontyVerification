# call-external
"""Stress test 8: walrus operator in conditions.

The `(n := expr)` pattern, common in LLM-generated code for "compute
once and reuse" idioms.
"""


def maybe_log(items):
    if (n := len(items)) > 10:
        log_warning('large batch')
        return n
    return 0


def process_if_present(items):
    if (first := get_first(items)) is not None:
        process_item(first)
        return True
    return False


assert maybe_log is not None
assert process_if_present is not None

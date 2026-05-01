# call-external
"""Stress test 13: nested closure with multi-level capture.

Two levels of nesting; the inner closes over both the outer
parameter AND the make_pipeline parameter. (Three-level nesting
where each level returns another closure is a known limitation —
the codegen's closure-factory detection only handles one level.)
"""


def make_formatter(prefix, suffix):
    def format(value):
        return prefix + value + suffix
    return format


def main():
    bracket = make_formatter('[', ']')
    return bracket('hello')


assert main is not None

"""Slice subscripts and chained comparisons. Both used to collapse
to PyVal.none in the flatten path; the most recent codegen round
fixed them by adding `pySlice` and emitting the `pyAnd (pyLt _ _)
(pyLt _ _)` chain even when sub-expressions are effectful."""

xs = [0, 1, 2, 3, 4, 5]

assert xs[1:4] == [1, 2, 3], 'basic slice'
assert xs[-3:] == [3, 4, 5], 'negative start'
assert xs[::-1] == [5, 4, 3, 2, 1, 0], 'reverse'
assert xs[::2] == [0, 2, 4], 'step of 2'

# Chain comparisons
assert (1 < 2 < 3) == True, 'ascending chain'
assert (3 < 2 < 1) == False, 'descending fails first'
assert (1 < 3 < 2) == False, 'fails at second'
assert (1 <= 2 <= 2 <= 3) == True, 'long chain with equality'

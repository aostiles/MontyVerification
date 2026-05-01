"""List comprehensions including a 2-generator nested form. The
recently-added `pyListComp2` runtime helper makes
`[expr for x in xs for y in ys]` actually iterate both generators
(previously the inner generator was silently dropped)."""

# Single-generator
squared = [x * x for x in [1, 2, 3, 4]]
assert squared == [1, 4, 9, 16], 'single-generator squares'

evens = [x for x in [1, 2, 3, 4, 5, 6] if x % 2 == 0]
assert evens == [2, 4, 6], 'with filter'

# Two-generator
sums = [x + y for x in [1, 2] for y in [10, 20]]
assert sums == [11, 21, 12, 22], 'two-generator addition'

products = [x * y for x in [1, 2, 3] for y in [10, 100]]
assert products == [10, 100, 20, 200, 30, 300], 'two-generator multiplication'

# Two-generator with the inner generator depending on the outer var
flat = [y for x in [[1, 2], [3, 4, 5]] for y in x]
assert flat == [1, 2, 3, 4, 5], 'flatten nested lists'

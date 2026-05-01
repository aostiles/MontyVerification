-- Properties for examples/slice_and_chain.py

/-- All eight assertions in the source pass: every slice produces the
    expected sub-list and every chain comparison evaluates to the
    documented boolean. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

/-- The basic slice `xs[1:4] == [1, 2, 3]` is decidable directly via
    `pySlice`. This is the value-level witness that the recently-added
    `pySlice` runtime helper produces real list slices instead of the
    previous `PyVal.none` collapse. -/
example :
    pySlice (PyVal.list [PyVal.int 0, PyVal.int 1, PyVal.int 2,
                          PyVal.int 3, PyVal.int 4, PyVal.int 5])
            (PyVal.int 1) (PyVal.int 4) PyVal.none
      = PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3] := by
  decide

/-- Negative-step reverse slice exercises the `step < 0` branch of
    `pySlice`'s index generator. -/
example :
    pySlice (PyVal.list [PyVal.int 0, PyVal.int 1, PyVal.int 2,
                          PyVal.int 3, PyVal.int 4, PyVal.int 5])
            PyVal.none PyVal.none (PyVal.int (-1))
      = PyVal.list [PyVal.int 5, PyVal.int 4, PyVal.int 3,
                     PyVal.int 2, PyVal.int 1, PyVal.int 0] := by
  decide

/-- `1 < 2 < 3` lowers to `pyAnd (pyLt 1 2) (pyLt 2 3)`, which
    decides to `true`. -/
example :
    pyAnd (pyLt (PyVal.int 1) (PyVal.int 2))
          (pyLt (PyVal.int 2) (PyVal.int 3))
      = PyVal.bool true := by
  decide

/-- `1 < 3 < 2` should fail at the second link. The chain
    short-circuits via `pyAnd`. -/
example :
    pyAnd (pyLt (PyVal.int 1) (PyVal.int 3))
          (pyLt (PyVal.int 3) (PyVal.int 2))
      = PyVal.bool false := by
  decide

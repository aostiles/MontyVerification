-- Properties for examples/list_comp.py

/-- All five comprehensions in the source produce the documented
    list: single-generator squaring, filtered evens, two two-generator
    cases, and the inner-uses-outer flatten. The whole module reduces. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

/-- Direct value-equality witness for the single-generator case via
    `pyListComp`. -/
example :
    (pyListComp (p := Perms.none)
        (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3, PyVal.int 4])
        (fun (x : PyVal) => pure (pyMul x x))
        (fun (_ : PyVal) => pure (PyVal.bool true))).run
      = .ok (PyVal.list [PyVal.int 1, PyVal.int 4, PyVal.int 9, PyVal.int 16]) := by
  native_decide

/-- Direct value-equality witness for the two-generator case via
    `pyListComp2`. The inner generator can mention the outer-loop
    variable; the iteration order matches argument order. -/
example :
    (pyListComp2 (p := Perms.none)
        (PyVal.list [PyVal.int 1, PyVal.int 2])
        (fun (_x : PyVal) => pure (PyVal.list [PyVal.int 10, PyVal.int 20]))
        (fun (x : PyVal) (y : PyVal) => pure (pyAdd x y))
        (fun (_x : PyVal) (_y : PyVal) => pure (PyVal.bool true))).run
      = .ok (PyVal.list [PyVal.int 11, PyVal.int 21,
                          PyVal.int 12, PyVal.int 22]) := by
  native_decide

/-- The inner-uses-outer flatten case: `[y for x in [[1,2],[3,4,5]] for y in x]`.
    The inner-iter closure receives the outer-loop variable and returns
    it as the inner iterable. -/
example :
    (pyListComp2 (p := Perms.none)
        (PyVal.list [PyVal.list [PyVal.int 1, PyVal.int 2],
                      PyVal.list [PyVal.int 3, PyVal.int 4, PyVal.int 5]])
        (fun (x : PyVal) => pure x)
        (fun (_x : PyVal) (y : PyVal) => pure y)
        (fun (_x : PyVal) (_y : PyVal) => pure (PyVal.bool true))).run
      = .ok (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3,
                          PyVal.int 4, PyVal.int 5]) := by
  native_decide

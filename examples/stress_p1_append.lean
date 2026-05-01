-- Properties for examples/stress_p1_append.py
-- P1 partial fix: list mutation via .append/.extend rebinding.

/-- The function compiles as a plain `def` (not `noncomputable`)
    because the appended elements are tracked via let-rebinding. -/
example : (collect_squares : PyVal → Eff Perms.none PyVal) = collect_squares := rfl

/-- Pure helper reduces by `native_decide` — the appended elements
    actually appear in the model now. -/
example :
    (collect_squares (PyVal.int 3)).run
      = .ok (PyVal.list [PyVal.int 9, PyVal.int 16]) := by native_decide

example :
    (collect_squares (PyVal.int 0)).run
      = .ok (PyVal.list [PyVal.int 0, PyVal.int 1]) := by native_decide

/-- The whole module — including the asserts about the mutation —
    passes via `native_decide`. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

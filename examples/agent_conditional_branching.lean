-- Properties for examples/agent_conditional_branching.py

/-! ## Effect-tracking witnesses -/

/-- `is_empty` is `Pure[bool]`. -/
example : (is_empty : PyVal → Eff Perms.none PyVal) = is_empty := rfl

/-- `search_with_fallback` is `Effect[Net, str]`. Both branches of
    the `if` reach `search_web`, so the function's perms are `Net`. -/
example :
    (search_with_fallback : PyVal → PyVal → Eff { net := true } PyVal)
      = search_with_fallback := rfl

/-! ## Pure helper reduces by computation -/

example :
    (is_empty (PyVal.str "")).run = .ok (PyVal.bool true) := by native_decide

example :
    (is_empty (PyVal.str "hi")).run = .ok (PyVal.bool false) := by native_decide

/-- The whole module — every assertion in the source — passes. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

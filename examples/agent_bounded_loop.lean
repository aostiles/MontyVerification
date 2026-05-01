-- Properties for examples/agent_bounded_loop.py

/-! ## Effect-tracking witnesses -/

/-- `render` is `Pure[str]`. -/
example : (render : PyVal → Eff Perms.none PyVal) = render := rfl

/-- `fetch_and_summarize` is `Effect[Net, str]`. The fetch reaches
    `search_web` (`Net`), and the per-item `render` is pure (lifted
    via `Eff.liftSub`). -/
example :
    (fetch_and_summarize : PyVal → Eff { net := true } PyVal)
      = fetch_and_summarize := rfl

/-! ## Pure helper reduces by computation -/

example :
    (render (PyVal.str "foo")).run = .ok (PyVal.str "* foo") := by
  native_decide

example :
    (render (PyVal.str "")).run = .ok (PyVal.str "* ") := by
  native_decide

/-- The whole module — every assertion in the source — passes. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

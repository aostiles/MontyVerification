-- Properties for examples/agent_no_annotations.py
--
-- The Python source has NO `Pure[]` / `Effect[]` annotations. The
-- codegen's effect inference walks each function body, unions the
-- effect sets of every external it calls (directly or transitively
-- through other local funcs), and uses that as the function's
-- declared perms. The proofs below witness the inferred types —
-- if the inference is wrong, the `rfl` line fails to elaborate.

/-! ## Inferred effect types -/

/-- `trim` calls no externals, so it's inferred as `Perms.none`
    (i.e. `Pure[str]`). -/
example : (trim : PyVal → PyVal → Eff Perms.none PyVal) = trim := rfl

/-- `fetch_one` calls `search_web` (a `Net` external), so the
    inference walks the call graph and emits it at
    `{ net := true }`. -/
example : (fetch_one : PyVal → Eff { net := true } PyVal) = fetch_one := rfl

/-- `research_and_notify` calls `fetch_one` (`Net`) and
    `send_email` (also `Net`), and `trim` (pure). The inferred
    perms are the union — `{ net := true }`. -/
example :
    (research_and_notify : PyVal → PyVal → Eff { net := true } PyVal)
      = research_and_notify := rfl

/-! ## Pure helper reduces by computation -/

example :
    (trim (PyVal.str "hello world") (PyVal.int 5)).run
      = .ok (PyVal.str "hello") := by native_decide

example :
    (trim (PyVal.str "hi") (PyVal.int 100)).run = .ok (PyVal.str "hi") := by
  native_decide

/-- The whole module — every assertion in the source — passes. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

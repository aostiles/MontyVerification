-- Properties for examples/agent_etl_pipeline.py

/-! ## Type-level: helpers are pure

Each helper has `Pure[bool]` / `Pure[int]`, witnessed by the
`Eff Perms.none` annotation. -/

example : (is_passing : PyVal → Eff Perms.none PyVal) = is_passing := rfl
example : (is_top : PyVal → Eff Perms.none PyVal) = is_top := rfl
example : (double : PyVal → Eff Perms.none PyVal) = double := rfl

/-! ## Helper-level reductions -/

example : (is_passing (PyVal.int 85)).run = .ok (PyVal.bool true) := by
  native_decide

example : (is_passing (PyVal.int 60)).run = .ok (PyVal.bool false) := by
  native_decide

example : (is_top (PyVal.int 95)).run = .ok (PyVal.bool true) := by
  native_decide

example : (double (PyVal.int 50)).run = .ok (PyVal.int 100) := by
  native_decide

/-! ## Pipeline-level reductions

The whole ETL pipeline is the assertion:
`«__module__».run = .ok PyVal.none` says every comprehension produces
the documented list and every length / value assertion in the
source decides true. This is the strongest possible verification
witness for a pure data-processing agent: the agent's plan, run
to completion, gives the user-visible answer the user expects. -/

example : («__module__».run = .ok PyVal.none) := by native_decide

/-! ## Direct value witnesses for the comprehensions

These prove the pipeline values independently of the surrounding
module body — useful as standalone theorems a downstream tool can
cite without re-running the whole module. -/

/-- The "passing" filter: scores ≥ 70 from the input list. -/
example :
    (pyListComp (p := Perms.none)
        (PyVal.list [PyVal.int 85, PyVal.int 92, PyVal.int 78, PyVal.int 95,
                      PyVal.int 60, PyVal.int 88, PyVal.int 73, PyVal.int 99,
                      PyVal.int 45, PyVal.int 81])
        (fun (s : PyVal) => pure s)
        (fun (s : PyVal) => pure (pyGe s (PyVal.int 70)))).run
      = .ok (PyVal.list [PyVal.int 85, PyVal.int 92, PyVal.int 78, PyVal.int 95,
                          PyVal.int 88, PyVal.int 73, PyVal.int 99, PyVal.int 81]) := by
  native_decide

/-- The "top doubled" pipeline: scores ≥ 90 doubled. -/
example :
    (pyListComp (p := Perms.none)
        (PyVal.list [PyVal.int 85, PyVal.int 92, PyVal.int 78, PyVal.int 95,
                      PyVal.int 60, PyVal.int 88, PyVal.int 73, PyVal.int 99,
                      PyVal.int 45, PyVal.int 81])
        (fun (s : PyVal) => pure (pyMul s (PyVal.int 2)))
        (fun (s : PyVal) => pure (pyGe s (PyVal.int 90)))).run
      = .ok (PyVal.list [PyVal.int 184, PyVal.int 190, PyVal.int 198]) := by
  native_decide

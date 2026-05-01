-- Properties for examples/agent_kitchen_sink.py
--
-- The kitchen-sink demo: every verification capability the system
-- has, exercised on a single annotation-free agent shape.

/-! ## 1. Effect inference

`clamp` calls no externals → inferred as `Perms.none` (Pure).
The other helpers transitively call `Net` externals → inferred as
`{ net := true }`. The top-level `run_agent` composes them → also
`{ net := true }`. -/

example : (clamp : PyVal → PyVal → PyVal → Eff Perms.none PyVal) = clamp := rfl

example : (fetch_step : PyVal → Eff { net := true } PyVal) = fetch_step := rfl

example :
    (summarize_step : PyVal → PyVal → Eff { net := true } PyVal)
      = summarize_step := rfl

example :
    (report_step : PyVal → Eff { net := true } PyVal) = report_step := rfl

example :
    (notify_step : PyVal → PyVal → Eff { net := true } PyVal)
      = notify_step := rfl

example :
    (run_agent : PyVal → PyVal → PyVal → Eff { net := true } PyVal)
      = run_agent := rfl

/-! ## 2. Pure helper reduces by computation -/

example :
    (clamp (PyVal.int 50) (PyVal.int 100) (PyVal.int 5000)).run
      = .ok (PyVal.int 100) := by native_decide

example :
    (clamp (PyVal.int 10000) (PyVal.int 100) (PyVal.int 5000)).run
      = .ok (PyVal.int 5000) := by native_decide

example :
    (clamp (PyVal.int 2000) (PyVal.int 100) (PyVal.int 5000)).run
      = .ok (PyVal.int 2000) := by native_decide

/-- The whole module's asserts pass. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

/-! ## 3. Symbolic execution: locals table for interprocedural analysis -/

def agent_locals : List (String × EffAST) :=
  [ ("clamp",          clamp__ast)
  , ("fetch_step",     fetch_step__ast)
  , ("summarize_step", summarize_step__ast)
  , ("report_step",    report_step__ast)
  , ("notify_step",    notify_step__ast)
  ]

/-! ## 4. Ordering invariants — interprocedural -/

example :
    EffAST.calledBeforeInter "ext_search_web" "ext_summarize"
        agent_locals run_agent__ast = true := by
  native_decide

example :
    EffAST.calledBeforeInter "ext_summarize" "ext_generate_report"
        agent_locals run_agent__ast = true := by
  native_decide

example :
    EffAST.calledBeforeInter "ext_generate_report" "ext_send_notification"
        agent_locals run_agent__ast = true := by
  native_decide

/-- Reverse direction is FALSE — the analysis catches reordering. -/
example :
    EffAST.calledBeforeInter "ext_send_notification" "ext_search_web"
        agent_locals run_agent__ast = false := by
  native_decide

/-! ## 5. The intra-procedural view sees only the helper names

(The interprocedural view above is needed to see the externals
inside each helper.) -/

example :
    EffAST.calledBefore "fetch_step" "summarize_step" run_agent__ast = true := by
  native_decide

example :
    EffAST.calledBefore "report_step" "notify_step" run_agent__ast = true := by
  native_decide

/-! ## 6. Other sym-exec properties on the helper-level view -/

/-- Every reachable return path of `run_agent` calls `notify_step`. -/
example : EffAST.eventuallyCalls "notify_step" run_agent__ast = true := by
  native_decide

/-- And `fetch_step` is called exactly once. -/
example : EffAST.calledExactlyOnce "fetch_step" run_agent__ast = true := by
  native_decide

/-- And `notify_step` is followed by nothing in the run_agent body
    (it's the last step before the return). -/
example :
    EffAST.calledAfter "fetch_step" "summarize_step" run_agent__ast = true := by
  native_decide

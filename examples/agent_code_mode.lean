-- Properties for examples/agent_code_mode.py
--
-- Code-mode integration demo: verifies the patterns that LLM code-mode
-- generates — for-loop dict accumulation and multi-step tool pipelines.

/-! ## Effect inference -/

example :
    (fetch_all : PyVal → Eff (EffAST.permsOf __extEnv __env fetch_all__ast) PyVal)
      = fetch_all := rfl

example :
    (process_and_report : PyVal → PyVal → Eff (EffAST.permsOf __extEnv __env process_and_report__ast) PyVal)
      = process_and_report := rfl

/-! ## Ordering on `process_and_report`

The pipeline: fetch_all → store_result → send_report. -/

example :
    EffAST.calledBefore "fetch_all" "ext_store_result"
        process_and_report__ast = true := by
  native_decide

example :
    EffAST.calledBefore "ext_store_result" "ext_send_report"
        process_and_report__ast = true := by
  native_decide

/-- Reversed direction is FALSE. -/
example :
    EffAST.calledBefore "ext_send_report" "ext_store_result"
        process_and_report__ast = false := by
  native_decide

/-! ## Interprocedural: see through `fetch_all` to the external

`calledBeforeInter` inlines `fetch_all__ast`. Since `get_weather`
is inside a loop that may execute 0 times, it's NOT guaranteed
to be called before `store_result` — the analysis correctly
reports this as false (if `cities` is empty, no weather is fetched).

But `fetch_all` as a helper IS called before `store_result`. -/

def code_mode_locals : List (String × EffAST) :=
  [ ("fetch_all", fetch_all__ast) ]

/-- The loop means get_weather isn't guaranteed (cities might be empty). -/
example :
    EffAST.calledBeforeInter "ext_get_weather" "ext_store_result"
        code_mode_locals process_and_report__ast = false := by
  native_decide

/-- But fetch_all (the helper) IS called before store_result. -/
example :
    EffAST.calledBeforeInter "fetch_all" "ext_store_result"
        code_mode_locals process_and_report__ast = true := by
  native_decide

/-- And store_result is called before send_report interprocedurally. -/
example :
    EffAST.calledBeforeInter "ext_store_result" "ext_send_report"
        code_mode_locals process_and_report__ast = true := by
  native_decide

/-! ## Resource guarantees -/

/-- Every path sends the report. -/
example :
    EffAST.eventuallyCalls "ext_send_report" process_and_report__ast = true := by
  native_decide

/-- Every path stores the result. -/
example :
    EffAST.eventuallyCalls "ext_store_result" process_and_report__ast = true := by
  native_decide

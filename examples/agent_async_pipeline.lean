-- Properties for examples/agent_async_pipeline.py
--
-- A document-processing agent with four helpers composed in
-- `run_pipeline`. Demonstrates:
--   1. Effect inference on unannotated functions
--   2. Interprocedural ordering across helper function boundaries
--   3. Resource cleanup guarantees
--   4. Exactly-once call guarantees

/-! ## Effect inference — each function gets precise effect types

The type signature `Eff (EffAST.permsOf __extEnv __env f__ast) PyVal`
means the effect type is *derived from the AST* — definitionally equal
to the union of the function's transitive external calls. The `rfl`
proofs witness that the codegen and the AST agree. -/

example :
    (fetch : PyVal → Eff (EffAST.permsOf __extEnv __env fetch__ast) PyVal)
      = fetch := rfl

example :
    (process : PyVal → Eff (EffAST.permsOf __extEnv __env process__ast) PyVal)
      = process := rfl

example :
    (notify_and_log : PyVal → PyVal → Eff (EffAST.permsOf __extEnv __env notify_and_log__ast) PyVal)
      = notify_and_log := rfl

example :
    (run_pipeline : PyVal → PyVal → Eff (EffAST.permsOf __extEnv __env run_pipeline__ast) PyVal)
      = run_pipeline := rfl

/-! ## Intra-procedural ordering on `run_pipeline`

The AST sees calls to the helper names (not the underlying externals).
We can verify the helpers are called in the right order. -/

example :
    EffAST.calledBefore "fetch" "process" run_pipeline__ast = true := by
  native_decide

example :
    EffAST.calledBefore "process" "notify_and_log" run_pipeline__ast = true := by
  native_decide

example :
    EffAST.calledBefore "fetch" "notify_and_log" run_pipeline__ast = true := by
  native_decide

/-! ## Interprocedural ordering — seeing through helpers

`calledBeforeInter` inlines each helper's AST at its call site,
so we can verify ordering on the *underlying externals* across
function boundaries. This is the key capability: proving that
`fetch_document` happens before `store_results` even though they
live in different functions. -/

def pipeline_locals : List (String × EffAST) :=
  [ ("fetch", fetch__ast)
  , ("process", process__ast)
  , ("notify_and_log", notify_and_log__ast)
  ]

/-- Documents are fetched before entities are extracted. -/
example :
    EffAST.calledBeforeInter "ext_fetch_document" "ext_extract_entities"
        pipeline_locals run_pipeline__ast = true := by
  native_decide

/-- Entities are extracted before results are stored. -/
example :
    EffAST.calledBeforeInter "ext_extract_entities" "ext_store_results"
        pipeline_locals run_pipeline__ast = true := by
  native_decide

/-- Results are stored before the user is notified. -/
example :
    EffAST.calledBeforeInter "ext_store_results" "ext_send_notification"
        pipeline_locals run_pipeline__ast = true := by
  native_decide

/-- Notification is sent before completion is logged. -/
example :
    EffAST.calledBeforeInter "ext_send_notification" "ext_log_completion"
        pipeline_locals run_pipeline__ast = true := by
  native_decide

/-- End-to-end: fetch happens before log (spans 3 function boundaries). -/
example :
    EffAST.calledBeforeInter "ext_fetch_document" "ext_log_completion"
        pipeline_locals run_pipeline__ast = true := by
  native_decide

/-- Sanity: reversed direction is FALSE. -/
example :
    EffAST.calledBeforeInter "ext_log_completion" "ext_fetch_document"
        pipeline_locals run_pipeline__ast = false := by
  native_decide

/-! ## Resource guarantees

Every path through `notify_and_log` logs completion. Since
`run_pipeline` always calls `notify_and_log`, every pipeline
execution is logged. -/

example :
    EffAST.eventuallyCalls "ext_log_completion" notify_and_log__ast = true := by
  native_decide

/-- Every path through `process` stores results. -/
example :
    EffAST.eventuallyCalls "ext_store_results" process__ast = true := by
  native_decide

/-! ## Exactly-once guarantees

Each external is called exactly once in its respective helper —
no double-fetch, no double-store. -/

example :
    EffAST.calledExactlyOnce "ext_fetch_document" fetch__ast = true := by
  native_decide

example :
    EffAST.calledExactlyOnce "ext_store_results" process__ast = true := by
  native_decide

example :
    EffAST.calledExactlyOnce "ext_log_completion" notify_and_log__ast = true := by
  native_decide

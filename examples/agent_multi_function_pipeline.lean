-- Properties for examples/agent_multi_function_pipeline.py
--
-- This example demonstrates *interprocedural* symbolic execution:
-- the ordering invariant "request_approval before process_payment
-- before log_transaction" is verified across a pipeline split
-- across multiple helper functions.
--
-- The codegen emits a separate `<name>__ast : EffAST` for each
-- function. We build a `locals` table mapping helper names to
-- their ASTs, and `EffAST.calledBeforeInter` walks the
-- `execute_payment__ast` value, inlining each helper at its call
-- site so calls inside the helpers count toward the must-set.

/-! ## The locals table (helper name → AST) -/

def payment_locals : List (String × EffAST) :=
  [ ("request_step",  request_step__ast)
  , ("process_step",  process_step__ast)
  , ("log_step",      log_step__ast)
  ]

/-! ## Effect inference still works on each helper -/

example :
    (request_step : PyVal → PyVal → Eff Perms.top PyVal) = request_step := rfl
example :
    (process_step : PyVal → PyVal → Eff Perms.top PyVal) = process_step := rfl
example :
    (log_step : PyVal → PyVal → Eff Perms.top PyVal) = log_step := rfl

/-! ## Intra-procedural sym-exec sees only the helper-level calls

The intra-procedural `calledBefore` walks `execute_payment__ast`
and sees three calls: `request_step`, `process_step`, `log_step`.
It can verify the ORDERING of these helpers: -/

example :
    EffAST.calledBefore "request_step" "process_step" execute_payment__ast = true := by
  native_decide

example :
    EffAST.calledBefore "process_step" "log_step" execute_payment__ast = true := by
  native_decide

/-- But it CANNOT see the externals inside each helper. The
    intra-procedural walker doesn't open `request_step__ast`, so a
    proof about `ext_request_approval` is vacuously `true` (the
    walker never hits a `.call "ext_request_approval"` site). The
    test below is `= true` as a vacuous true; the interprocedural
    version below is the meaningful one. -/
example :
    EffAST.calledBefore "ext_request_approval" "ext_process_payment" execute_payment__ast = true := by
  native_decide

/-! ## Interprocedural sym-exec inlines the helpers

`calledBeforeInter` consults the `payment_locals` table at each
call site, recursing into the helper's AST. Now the externals
inside each helper are visible, and we can verify ordering invariants
that span function boundaries. -/

example :
    EffAST.calledBeforeInter "ext_request_approval" "ext_process_payment"
        payment_locals execute_payment__ast = true := by
  native_decide

example :
    EffAST.calledBeforeInter "ext_request_approval" "ext_log_transaction"
        payment_locals execute_payment__ast = true := by
  native_decide

example :
    EffAST.calledBeforeInter "ext_process_payment" "ext_log_transaction"
        payment_locals execute_payment__ast = true := by
  native_decide

/-- Sanity: the reverse direction is FALSE. The interprocedural
    analysis catches reordering bugs across function boundaries.
    Note: this is provably false, not vacuously — `ext_process_payment`
    IS called (transitively, via `process_step`), and at that call
    site the must-set does NOT contain `ext_log_transaction`. -/
example :
    EffAST.calledBeforeInter "ext_log_transaction" "ext_process_payment"
        payment_locals execute_payment__ast = false := by
  native_decide

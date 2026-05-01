-- Properties for examples/agent_payment_workflow.py
--
-- This example uses the codegen-emitted `EffAST` representation
-- (Path C — defunctionalized free monad with HOAS bind continuations
-- and structural branches/handlers) to verify *ordering invariants*
-- on the agent's tool calls. No `Pure[]`/`Effect[]` annotations are
-- needed in the Python source — the codegen extracts the call
-- sequence directly from the function body.
--
-- The decision procedure `EffAST.calledBefore` walks the AST by
-- forward dataflow, threading the set of names called so far on the
-- current path. At each call site to the target name, it checks the
-- prerequisite is in the set. Branches and try/except both arms are
-- intersected. Loops conservatively contribute nothing to the
-- must-set after them. All proofs discharge by `native_decide`.

/-! ## Effect inference still works -/

example :
    (execute_payment : PyVal → PyVal → Eff Perms.top PyVal) = execute_payment := rfl

/-! ## Ordering invariants — the actual story.

These four theorems are the verification value. Each one is
discharged by `native_decide` walking the `execute_payment__ast`
value emitted by the codegen. -/

/-- Approval is requested before payment is processed. -/
example :
    EffAST.calledBefore "ext_request_approval" "ext_process_payment"
        execute_payment__ast = true := by
  native_decide

/-- Approval is requested before the transaction is logged. -/
example :
    EffAST.calledBefore "ext_request_approval" "ext_log_transaction"
        execute_payment__ast = true := by
  native_decide

/-- Payment is processed before the transaction is logged. -/
example :
    EffAST.calledBefore "ext_process_payment" "ext_log_transaction"
        execute_payment__ast = true := by
  native_decide

/-- Sanity-check the analysis catches reversed orderings: log is
    NOT called before process. If the decision procedure were
    monotonically `true`, this `= false` proof would fail. -/
example :
    EffAST.calledBefore "ext_log_transaction" "ext_process_payment"
        execute_payment__ast = false := by
  native_decide

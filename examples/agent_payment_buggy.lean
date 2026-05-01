-- Properties for examples/agent_payment_buggy.py
--
-- Companion to agent_payment_workflow.lean: this version of the
-- agent has a cached-payment fast path that skips `request_approval`.
-- The symbolic-execution analysis correctly reports that the
-- ordering invariant FAILS — there exists a path (the cached one)
-- from entry to `process_payment` that doesn't go through
-- `request_approval`.

/-- The agent compiles fine — the bug is semantic, not syntactic. -/
example :
    (execute_payment : PyVal → PyVal → PyVal → Eff Perms.top PyVal)
      = execute_payment := rfl

/-- The ordering invariant FAILS: there is a branch (the cached one)
    where `process_payment` runs without a preceding
    `request_approval`. The decision procedure walks both branches of
    the `branchOn` constructor and intersects their must-sets — the
    cached branch's must-set is empty for `request_approval`, so the
    intersection is empty, and the check at the `process_payment`
    call site fails.

    Proving this `= false` (rather than just observing the missing
    `true` proof) is the load-bearing test: it demonstrates that the
    analysis is sound in the negative direction too. -/
example :
    EffAST.calledBefore "ext_request_approval" "ext_process_payment"
        execute_payment__ast = false := by
  native_decide

/-- Logging still happens unconditionally on both branches, so the
    ordering "process before log" still holds. The bug is specifically
    in the approval gate, not the logging. -/
example :
    EffAST.calledBefore "ext_process_payment" "ext_log_transaction"
        execute_payment__ast = true := by
  native_decide

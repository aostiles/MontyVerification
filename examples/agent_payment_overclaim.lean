-- EXPECT: type-error
--
-- Negative example: this file claims the payment workflow respects
-- the approval-before-process invariant, but the Python source has
-- a cached fast path that bypasses approval. The symbolic-execution
-- analysis should catch the lie and reject the file.
--
-- The runner expects this file to FAIL compilation. If it ever
-- compiles cleanly, the symbolic-execution layer has a soundness
-- hole and the runner will report it.

example :
    EffAST.calledBefore "ext_request_approval" "ext_process_payment"
        execute_payment__ast = true := by
  native_decide

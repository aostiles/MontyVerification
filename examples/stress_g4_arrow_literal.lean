-- Regression for G4 (string-literal corruption via the bind-wrap
-- rewriting). The Python source contains a string literal with the
-- exact sequence `← (` that the OLD post-processing would corrupt.

example :
    (log_message : PyVal → Eff { net := true } PyVal) = log_message := rfl

/-- Sym-exec witness that the function still has the right shape
    after the G4 fix. -/
example :
    EffAST.eventuallyCalls "ext_ext_log_msg" log_message__ast = true := by
  native_decide

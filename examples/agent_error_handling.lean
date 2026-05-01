-- Properties for examples/agent_error_handling.py

/-! ## Effect-tracking witnesses for the error-handling agent -/

/-- `safe_lookup` is `Effect[Net, str]`. The try-body uses
    `search_web` (`Net`) and the except-handler uses `send_email`
    (also `Net`); both must be covered by the function's declared
    perms. The `try/except` lowering threads both branches' types
    through `Eff.tryCatch`, which expects them to share a perms
    parameter. -/
example :
    (safe_lookup : PyVal → PyVal → Eff { net := true } PyVal)
      = safe_lookup := rfl

example : (ext_search_web : PyVal → Eff { net := true } PyVal) = ext_search_web := rfl
example : (ext_send_email : PyVal → PyVal → Eff { net := true } PyVal) = ext_send_email := rfl

/-! ## A `Pure` annotation would be rejected. -/

example : ¬ Perms.sub { net := true } Perms.none := by decide

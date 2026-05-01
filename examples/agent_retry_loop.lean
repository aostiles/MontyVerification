-- Properties for examples/agent_retry_loop.py

/-! ## Effect-tracking witnesses for the retry loop -/

/-- `attempt` is `Effect[Net, str]`. Single tool call wrapper. -/
example : (attempt : PyVal → Eff { net := true } PyVal) = attempt := rfl

/-- `retry_search` is `Effect[Net, str]`. The bounded `for _ in
    range(max_attempts)` loop iterates `attempt` (which is `Net`),
    so the function's perms are `Net` regardless of how many
    iterations fire. -/
example :
    (retry_search : PyVal → PyVal → Eff { net := true } PyVal)
      = retry_search := rfl

/-! ## The retry loop terminates and stays at Net.

The bounded `for _ in range(N)` loop is what guarantees totality.
A `while True` retry would also stay at `Net`, but our `pyWhile`
fuel bound is what would catch it then. -/

example : Perms.sub Perms.none { net := true } := by decide
example : ¬ Perms.sub { net := true } Perms.none := by decide

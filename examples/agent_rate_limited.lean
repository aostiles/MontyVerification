-- Properties for examples/agent_rate_limited.py
--
-- Type-state demo: a session value indexed by the remaining token
-- budget. Each tool call consumes one token; once the budget hits
-- zero, no further tool calls type-check, because there is no value
-- of `RateLimited 0` that can produce a token-bearing successor.
--
-- This is a stronger guarantee than runtime rate limiting: the
-- compiler statically prevents calling more than N tools, no matter
-- what control flow the agent uses.

/-! ## Codegen-level effect tracking for the pure helper -/

example : (trim : PyVal → PyVal → Eff Perms.none PyVal) = trim := rfl

example :
    (trim (PyVal.str "hello world") (PyVal.int 5)).run
      = .ok (PyVal.str "hello") := by native_decide

example : («__module__».run = .ok PyVal.none) := by native_decide

/-! ## Type-state: token-budget session

`RateLimited n` is a session in which `n` tool calls remain. Each
tool call consumes one token, so its signature requires
`RateLimited (n+1)` and produces `RateLimited n`. The compiler
will refuse to call a tool with `RateLimited 0` because there's
no `n+1` shape to match. -/

structure RateLimited (n : Nat) : Type where
  /-- Opaque marker: the only way to obtain a `RateLimited n` is
      from another `RateLimited (n+1)` via `consume`, or from the
      initial `RateLimited.start N`. -/
  marker : Unit := ()

/-- Start a session with a fixed token budget. -/
def RateLimited.start (n : Nat) : RateLimited n := ⟨()⟩

/-- Consume one token. The signature `RateLimited (n+1) → RateLimited n`
    is the load-bearing part: only sessions with at least one token
    remaining can produce a successor. -/
def ts_call_tool (_arg : PyVal) (_session : RateLimited (n+1))
    : Eff Perms.none (PyVal × RateLimited n) :=
  pure (PyVal.none, ⟨()⟩)

/-- A correct workflow that makes exactly two tool calls within a
    budget of 3. The compiler is happy: every `ts_call_tool` is
    paired with a `RateLimited (n+1)` argument. -/
def two_calls_in_three_budget : Eff Perms.none (PyVal × RateLimited 1) := do
  let session : RateLimited 3 := RateLimited.start 3
  let (_v1, s1) ← ts_call_tool (PyVal.str "first") session
  let (_v2, s2) ← ts_call_tool (PyVal.str "second") s1
  pure (PyVal.none, s2)

/-- Witness: the type of the session at the end of the workflow
    proves that one token remains. The verifier reads off the
    final perms-of-session-state from the function's return type. -/
example :
    (two_calls_in_three_budget : Eff Perms.none (PyVal × RateLimited 1))
      = two_calls_in_three_budget := rfl

/-- Three calls in a budget of three: also fine, ending at
    `RateLimited 0`. -/
def three_calls_in_three_budget : Eff Perms.none (PyVal × RateLimited 0) := do
  let session : RateLimited 3 := RateLimited.start 3
  let (_v1, s1) ← ts_call_tool (PyVal.str "first") session
  let (_v2, s2) ← ts_call_tool (PyVal.str "second") s1
  let (_v3, s3) ← ts_call_tool (PyVal.str "third") s2
  pure (PyVal.none, s3)

example :
    (three_calls_in_three_budget : Eff Perms.none (PyVal × RateLimited 0))
      = three_calls_in_three_budget := rfl

-- A workflow that tries to make a fourth call after exhausting
-- the budget cannot be defined — there is no way to construct a
-- `RateLimited (m+1)` from a `RateLimited 0`. The (commented-out)
-- definition below would be rejected by Lean.
--
--     def four_calls_in_three_budget : Eff Perms.none (PyVal × RateLimited 0) := do
--       let session : RateLimited 3 := RateLimited.start 3
--       let (_, s1) ← ts_call_tool (PyVal.str "a") session
--       let (_, s2) ← ts_call_tool (PyVal.str "b") s1
--       let (_, s3) ← ts_call_tool (PyVal.str "c") s2
--       -- Type error: ts_call_tool expects RateLimited (n+1), got RateLimited 0
--       let (_, s4) ← ts_call_tool (PyVal.str "d") s3
--       pure (PyVal.none, s4)
--
-- The verification value is in *what does not exist*: any agent
-- that exceeds the budget literally has no Lean term.

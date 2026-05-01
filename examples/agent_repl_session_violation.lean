-- Properties for examples/agent_repl_session_violation.py
--
-- EXPECT: type-error
--
-- This is a NEGATIVE example. The agent tries to skip the
-- summarize turn and call generate_report directly on a fresh
-- session. The session-state type forces the type checker to
-- reject the program.

structure Session (s : Bool) (r : Bool) : Type where

def repl_init : Session false false := {}

def s_summarize {s r : Bool} (_state : Session s r) (_text : PyVal)
    : Eff Perms.none (PyVal × Session true r) :=
  pure (PyVal.none, {})

def s_generate_report {r : Bool} (_state : Session true r) (_summary : PyVal)
    : Eff Perms.none (PyVal × Session true true) :=
  pure (PyVal.none, {})

-- The malicious / buggy agent: tries to call generate_report on
-- the initial session, which has type `Session false false`.
-- `s_generate_report` requires `Session true _`. Lean rejects.
def malicious_skip_summarize (text : PyVal)
    : Eff Perms.none (PyVal × Session true true) := do
  let state0 := repl_init
  let (report, state1) ← Eff.liftSub (s_generate_report state0 text)
  pure (report, state1)

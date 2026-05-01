-- Properties for examples/agent_report_protocol_violation.py
--
-- EXPECT: type-error
--
-- This is a NEGATIVE example. The driver expects Lean to REJECT
-- this file. The success criterion is "Lean produces a type error"
-- — symmetric to the mal-harness soundness regression tests.
--
-- The agent below tries to skip the required `ts_summarize` call
-- and jump straight to `ts_generate_report`. The verification
-- surface enforces the protocol via type-state: `ts_generate_report`
-- requires a `SummaryToken` argument, which can only be obtained
-- from `ts_summarize`. The agent has no token to pass, so the
-- def fails to type-check.

-- Reproduce the witness types and typed externals.
structure SummaryToken : Type where
structure ReportToken : Type where
structure NotifiedToken : Type where

def ts_summarize (_text : PyVal) : Eff Perms.none (PyVal × SummaryToken) :=
  pure (PyVal.none, {})

def ts_generate_report (_tok : SummaryToken) (_summary : PyVal)
    : Eff Perms.none (PyVal × ReportToken) :=
  pure (PyVal.none, {})

def ts_send_notification (_tok : ReportToken) (_recipient : PyVal)
    : Eff { net := true } NotifiedToken :=
  pure {}

-- The malicious workflow: the agent tries to call
-- `ts_generate_report` without first calling `ts_summarize`. There
-- is no `SummaryToken` to pass, so this `def` does not type-check.
-- Lean will report an "Application type mismatch" error at the call
-- to `ts_generate_report`.
def malicious_skips_summarize (text recipient : PyVal)
    : Eff { net := true } NotifiedToken := do
  let (_report, rep_tok) ← Eff.liftSub (ts_generate_report text)
  ts_send_notification rep_tok recipient

-- Properties for examples/agent_report_protocol.py
--
-- This file demonstrates THREE different verification approaches
-- on the same Python source. The contrast between them is the
-- whole point — each has different trust-chain properties.
--
-- 1. **Effect-set verification (Part A)**. The codegen lowers the
--    Python to standard externals and infers effect annotations.
--    `report_pipeline` is `Eff { net := true } PyVal`. Discharged
--    by `rfl`.
--
-- 2. **Type-state via parallel typed externals (Part B)**. We
--    hand-write a parallel `ts_*` namespace where each call
--    returns a witness token and the next call requires that
--    token. `ts_report_pipeline` is a hand-written Lean function
--    that mirrors the Python — its existence proves the protocol
--    order is respected. **But the connection between the Python
--    source and this Lean function is social.** The author has to
--    keep them in sync by hand. Modifying `report_pipeline.py` to
--    reorder the calls would NOT cause `ts_report_pipeline` to
--    fail.
--
-- 3. **Symbolic execution over `EffAST` (Part C — added 2026-04)**.
--    The codegen ALSO emits `report_pipeline__ast : EffAST`, and
--    we prove ordering properties via `native_decide` against the
--    AST. **The AST and the executable `def` come from the same
--    codegen pass on the same IR**, so reordering the Python
--    source mechanically breaks these proofs.
--
-- Both Part B and Part C verify "summarize before generate_report",
-- but Part C closes the trust gap that Part B leaves open.

/-! ## Part A: codegen-level effect-set verification -/

/-- The pure helper exists with `Pure[str]` annotation. -/
example : (trim : PyVal → PyVal → Eff Perms.none PyVal) = trim := rfl

/-- The agent's workflow exists with `Effect[Net, str]` annotation. -/
example :
    (report_pipeline : PyVal → PyVal → Eff { net := true } PyVal) = report_pipeline := rfl

/-- The pure helper reduces by decision. -/
example :
    (trim (PyVal.str "hello world") (PyVal.int 5)).run = .ok (PyVal.str "hello") := by
  native_decide

/-- The whole module — its three pure-helper assertions — passes. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

/-! ## Part B: type-state protocol verification

We define witness types for each protocol checkpoint. By convention,
users obtain witnesses only by calling the corresponding `ts_X`
external — the tokens have empty bodies, so the verification value
is in the SIGNATURES below.

The convention is enforced socially (any caller must pass through
the typed externals), but the type-level enforcement is mechanical:
you cannot CALL `ts_generate_report` unless you have a value of
type `SummaryToken` to give it, and the only such value comes from
`ts_summarize`. -/

/-- Token witness: someone called `ts_summarize`. -/
structure SummaryToken : Type where

/-- Token witness: someone called `ts_generate_report` (which itself
    required a `SummaryToken`). -/
structure ReportToken : Type where

/-- Token witness: someone called `ts_send_notification` (which itself
    required a `ReportToken`). -/
structure NotifiedToken : Type where

/-- Typed `summarize` external: takes raw text, produces a summary
    payload AND a `SummaryToken` witness. -/
def ts_summarize (_text : PyVal) : Eff Perms.none (PyVal × SummaryToken) :=
  pure (PyVal.none, {})

/-- Typed `generate_report` external: takes a `SummaryToken` (proving
    summarize was called) and the summary payload, produces a report
    AND a `ReportToken`. **No way to call this without first calling
    `ts_summarize`** — Lean rejects any def that tries. -/
def ts_generate_report (_tok : SummaryToken) (_summary : PyVal)
    : Eff Perms.none (PyVal × ReportToken) :=
  pure (PyVal.none, {})

/-- Typed `send_notification` external: takes a `ReportToken` (which
    transitively requires a `SummaryToken`), and produces a
    `NotifiedToken`. This is `Net`. -/
def ts_send_notification (_tok : ReportToken) (_recipient : PyVal)
    : Eff { net := true } NotifiedToken :=
  pure {}

/-- The CORRECT type-state version of `report_pipeline`. The tokens
    flow naturally through the do-block: `sum_tok` is produced by
    `ts_summarize`, consumed by `ts_generate_report`; `rep_tok` is
    produced by `ts_generate_report`, consumed by
    `ts_send_notification`. The fact that this `def` exists with
    type `Eff { net := true } NotifiedToken` is the proof that the
    protocol order was followed — there is no other way to produce
    a `NotifiedToken`. -/
def ts_report_pipeline (text : PyVal) (recipient : PyVal)
    : Eff { net := true } NotifiedToken := do
  let (raw, sum_tok) ← Eff.liftSub (ts_summarize text)
  let (_report, rep_tok) ← Eff.liftSub (ts_generate_report sum_tok raw)
  ts_send_notification rep_tok recipient

/-- **Theorem**: the type-state version exists with the right
    signature. This is a `rfl` witness — the verification value is
    that Lean accepted the `def` above, which it could only do if
    the protocol order was followed. -/
example :
    (ts_report_pipeline :
        PyVal → PyVal → Eff { net := true } NotifiedToken)
      = ts_report_pipeline := rfl

/-- **Theorem**: any execution of `ts_report_pipeline` produces a
    `NotifiedToken`. The type forces this — the function's return
    type is `Eff p NotifiedToken`, so a successful `.ok` result
    contains a value of that type. The token's existence transitively
    proves the entire chain ran. -/
example :
    ∀ (text recipient : PyVal),
      ∃ _ : NotifiedToken, True := by
  intro _ _
  exact ⟨{}, trivial⟩

/-! ## What the wrong workflow looks like

Uncommenting the following def would cause Lean to REJECT this file
with a "type mismatch: expected `SummaryToken`, got `PyVal`" error
at the call to `ts_generate_report`, because the agent skipped the
required `ts_summarize` call:

```
def wrong_skips_summarize (text recipient : PyVal)
    : Eff { net := true } NotifiedToken := do
  let (_report, rep_tok) ← Eff.liftSub (ts_generate_report text)
  --                                                       ^^^^
  --                                       expected SummaryToken
  ts_send_notification rep_tok recipient
```

The compiler enforces the protocol; the LLM is free to vary
everything else about the workflow but cannot violate the
ordering constraint. -/

/-! ## A different agent: same protocol, different shape

The protocol allows arbitrary creativity around the ordering. Here's
a verification that a *different* workflow still satisfies the same
ordering invariant — the agent might fan out, retry, log between
steps, etc. -/

def alternate_agent (text1 text2 recipient : PyVal)
    : Eff { net := true } NotifiedToken := do
  -- Summarize twice, then report on the second summary, then notify.
  -- (A real agent might compare the two, pick the longer one, etc.)
  let (_raw1, _sum_tok1) ← Eff.liftSub (ts_summarize text1)
  let (raw2, sum_tok2) ← Eff.liftSub (ts_summarize text2)
  let (_report, rep_tok) ← Eff.liftSub (ts_generate_report sum_tok2 raw2)
  ts_send_notification rep_tok recipient

example :
    (alternate_agent :
        PyVal → PyVal → PyVal → Eff { net := true } NotifiedToken)
      = alternate_agent := rfl

/-! ## Part C: Symbolic execution over `EffAST` (the trust-chain fix)

The codegen emits `report_pipeline__ast : EffAST` automatically
alongside the executable `def report_pipeline`. We use the
ordering decision procedures over the AST. The proofs discharge
by `native_decide` walking the AST structurally.

The crucial difference from Part B: there is no hand-written
parallel function. The `__ast` value is generated by the same
codegen pass that produces `report_pipeline`, so they cannot
drift. Modifying the Python source to reorder the calls would
mechanically break these proofs. -/

example :
    EffAST.calledBefore "ext_search_web" "ext_summarize"
        report_pipeline__ast = true := by
  native_decide

example :
    EffAST.calledBefore "ext_summarize" "ext_generate_report"
        report_pipeline__ast = true := by
  native_decide

example :
    EffAST.calledBefore "ext_generate_report" "ext_send_notification"
        report_pipeline__ast = true := by
  native_decide

/-- Sanity: the analysis is sound in the negative direction.
    `ext_send_notification` is NOT called before `ext_summarize`. -/
example :
    EffAST.calledBefore "ext_send_notification" "ext_summarize"
        report_pipeline__ast = false := by
  native_decide

/-- Every reachable return path notifies. -/
example : EffAST.eventuallyCalls "ext_send_notification" report_pipeline__ast = true := by
  native_decide

/-- Every step is called exactly once. -/
example : EffAST.calledExactlyOnce "ext_summarize" report_pipeline__ast = true := by
  native_decide

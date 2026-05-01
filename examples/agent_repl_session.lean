-- Properties for examples/agent_repl_session.py
--
-- This file demonstrates how a multi-turn REPL session is verified
-- by indexing the session-state TYPE on which protocol checkpoints
-- have been reached. Each tool call advances the type, and each
-- turn's signature requires/produces the right type. The type
-- system enforces the protocol order across the whole session.

/-! ## Part A: codegen-level pure-helper verification -/

example : (trim : PyVal → PyVal → Eff Perms.none PyVal) = trim := rfl

example :
    (trim (PyVal.str "hello world") (PyVal.int 5)).run = .ok (PyVal.str "hello") := by
  native_decide

example : («__module__».run = .ok PyVal.none) := by native_decide

/-! ## Part B: dependent session state for multi-turn protocol checking

`Session s r` is the REPL state type, indexed by:
  * `s : Bool` — whether `summarize` has been called this session
  * `r : Bool` — whether `generate_report` has been called this session

The state itself has no fields (we don't model variable bindings or
chat history here — those would be the body of the structure in a
real implementation). The verification value is entirely in the
TYPE: a `Session true false` is a session in which exactly the
"summarized" checkpoint has been reached. The next call must
have a signature that accepts this type as input. -/

structure Session (s : Bool) (r : Bool) : Type where

/-- A fresh REPL session: nothing has been called yet. -/
def repl_init : Session false false := {}

/-! ## Tools that advance the session state's type

Each tool's signature encodes its protocol contract:

  * `summarize` is available in any state, advances `s` to `true`.
  * `generate_report` requires `s = true`, advances `r` to `true`.
  * `send_notification` requires `r = true`, leaves both flags as-is.

The flag *position* in the input type is the precondition; the
flag position in the output type is the postcondition. -/

def s_summarize {s r : Bool} (_state : Session s r) (_text : PyVal)
    : Eff Perms.none (PyVal × Session true r) :=
  pure (PyVal.none, {})

def s_generate_report {r : Bool} (_state : Session true r) (_summary : PyVal)
    : Eff Perms.none (PyVal × Session true true) :=
  pure (PyVal.none, {})

def s_send_notification {s : Bool} (_state : Session s true) (_recipient : PyVal)
    : Eff { net := true } (Session s true) :=
  pure {}

/-! ## Modeling individual REPL turns

Each turn is a small program that takes the previous turn's session
state and produces an updated state. The turn's TYPE captures the
protocol position: `turn1` runs from a fresh session, `turn2`
requires the post-summarize state, `turn3` requires the post-report
state. -/

/-- Turn 1: agent summarizes the input text. -/
def turn1 (state : Session false false) (text : PyVal)
    : Eff Perms.none (PyVal × Session true false) :=
  s_summarize state text

/-- Turn 2: agent generates a report from the summary. The input
    type forces summarize to have been called in a previous turn —
    `Session true false` is the type the previous turn produced. -/
def turn2 (state : Session true false) (summary : PyVal)
    : Eff Perms.none (PyVal × Session true true) :=
  s_generate_report state summary

/-- Turn 3: agent sends the notification. Input type forces both
    earlier checkpoints. -/
def turn3 (state : Session true true) (recipient : PyVal)
    : Eff { net := true } (Session true true) :=
  s_send_notification state recipient

/-- A complete session that chains the three turns. The state value
    threads through the do-block; its TYPE evolves at each step.
    The fact that this `def` exists at type
    `Eff { net := true } (Session true true)` is the proof that
    the session followed the protocol from start to finish. -/
def full_session (text recipient : PyVal)
    : Eff { net := true } (Session true true) := do
  let state0 := repl_init
  let (summary, state1) ← Eff.liftSub (turn1 state0 text)
  let (_report, state2) ← Eff.liftSub (turn2 state1 summary)
  turn3 state2 recipient

/-! ## Verification

The type-level guarantee is that you cannot construct
`full_session` without going through the right sequence. We can
also write theorems about specific session executions. -/

example :
    (full_session : PyVal → PyVal → Eff { net := true } (Session true true))
      = full_session := rfl

/-- The session type chain is well-formed: each turn's output
    matches the next turn's input. -/
example : (turn1 : Session false false → PyVal → Eff Perms.none (PyVal × Session true false))
    = turn1 := rfl
example : (turn2 : Session true false → PyVal → Eff Perms.none (PyVal × Session true true))
    = turn2 := rfl
example : (turn3 : Session true true → PyVal → Eff { net := true } (Session true true))
    = turn3 := rfl

/-! ## Different sessions, same invariant

The invariant constrains the *order* of tool calls but leaves the
agent free to vary everything else: which inputs, how many times,
what the host code does between calls, etc. Here are two valid
sessions with very different shapes. -/

/-- A "verbose" session that summarizes twice (e.g. the user asked
    for a refinement) before generating the report. Both summaries
    advance the state type the same way (summarize → summarize →
    state stays at `Session true _`), so the second call is fine. -/
def verbose_session (text1 text2 recipient : PyVal)
    : Eff { net := true } (Session true true) := do
  let state0 := repl_init
  let (_s1, state1) ← Eff.liftSub (s_summarize state0 text1)
  let (s2, state2) ← Eff.liftSub (s_summarize state1 text2)
  let (_report, state3) ← Eff.liftSub (s_generate_report state2 s2)
  s_send_notification state3 recipient

example :
    (verbose_session : PyVal → PyVal → PyVal → Eff { net := true } (Session true true))
      = verbose_session := rfl

/-- A "fan-out" session that generates two reports from the same
    summary. After the first `s_generate_report` the state is
    `Session true true`; the second call still has the right input
    type. The flag tracks "at-least-once" not "exactly-once". -/
def fan_out_session (text recipient : PyVal)
    : Eff { net := true } (Session true true) := do
  let state0 := repl_init
  let (summary, state1) ← Eff.liftSub (s_summarize state0 text)
  let (_r1, state2) ← Eff.liftSub (s_generate_report state1 summary)
  let (_r2, state3) ← Eff.liftSub (s_generate_report state2 summary)
  s_send_notification state3 recipient

example :
    (fan_out_session : PyVal → PyVal → Eff { net := true } (Session true true))
      = fan_out_session := rfl

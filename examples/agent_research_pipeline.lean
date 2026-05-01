-- Properties for examples/agent_research_pipeline.py

/-! ## Type-level effect-tracking witnesses

These four `def` declarations are the entire type-level verification:
the file *type-checks*, so each function has the effect annotation it
claims. If `research_and_notify` had been declared `Pure[str]`, Lean
would reject this file at the call to `ext_search_web`. The fact that
the file compiles is the proof. -/

/-- `truncate` is `Pure[str]` — its body uses no externals and the
    type-checker confirms `Eff Perms.none`. -/
example : (truncate : PyVal → PyVal → Eff Perms.none PyVal) = truncate := rfl

/-- `research_and_notify` is `Effect[Net, str]`. Its body reaches both
    `ext_search_web` and `ext_send_email`, both `Net` externals, and
    `truncate` is lifted in via `Eff.liftSub` (decided by `Perms.none ⊆
    { net := true }`). -/
example :
    (research_and_notify : PyVal → PyVal → Eff { net := true } PyVal)
      = research_and_notify := rfl

/-- `ext_search_web` and `ext_send_email` are themselves `Net` —
    that's how the codegen pinned them, so a `Pure` caller is rejected. -/
example : (ext_search_web : PyVal → Eff { net := true } PyVal) = ext_search_web := rfl
example : (ext_send_email : PyVal → PyVal → Eff { net := true } PyVal) = ext_send_email := rfl

/-! ## Value-level reduction witnesses for the pure helper

These prove that the assertion in the source isn't vacuous: the pure
helper actually computes the documented value, decided by `rfl` /
`decide`. -/

/-- `truncate('hello world', 5) = 'hello'`. The `pySlice` runtime
    helper produces a real string slice, so the equality decides. -/
example :
    (truncate (PyVal.str "hello world") (PyVal.int 5)).run
      = .ok (PyVal.str "hello") := by native_decide

/-- `truncate` is the identity on inputs shorter than the limit. -/
example :
    (truncate (PyVal.str "hi") (PyVal.int 100)).run = .ok (PyVal.str "hi") := by
  native_decide

/-- The empty string is fixed. -/
example :
    (truncate (PyVal.str "") (PyVal.int 10)).run = .ok (PyVal.str "") := by
  native_decide

/-- The whole module — every assertion in the source — runs to
    `.ok PyVal.none`. The Net externals stub to `PyVal.none` in our
    model, but the *pure* assertions verify by reduction. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

/-! ## Sub-permission relation witnesses

The `Eff.liftSub` calls in `research_and_notify` carry decidable
proofs of `Perms.none ⊆ { net := true }`. We can witness those
proofs (and the unsafe direction's refutation) directly. -/

example : Perms.sub Perms.none { net := true } := by decide
example : ¬ Perms.sub { net := true } Perms.none := by decide
example : ¬ Perms.sub { net := true } { fs := true } := by decide

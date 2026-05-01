-- Properties for examples/effect_protocol.py

/-- The pure portion of the module body (the two assertions) reduces
    to `.ok PyVal.none`. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

/-- `pure_helper` has type `Eff Perms.none PyVal`. The `def` exists
    with that type — that's the type-level effect-tracking witness.
    If the body had called `ext_ext_notify` (a `Net` external), this
    annotation would not type-check. -/
example : (pure_helper : PyVal → Eff Perms.none PyVal) = pure_helper := rfl

/-- `net_caller` has type `Eff { net := true } PyVal`. Its body calls
    both `pure_helper` (a sub-permission helper, lifted via
    `Eff.liftSub`) and `ext_ext_notify` (a `Net` external). The
    `def` typechecks because `decide` can discharge
    `Perms.none.sub { net := true }`. -/
example :
    (net_caller : PyVal → Eff { net := true } PyVal) = net_caller := rfl

/-- `pure_helper(21) == 42` is provable by `rfl` because the body
    uses no axioms and reduces directly. -/
example : (pure_helper (PyVal.int 21)).run = .ok (PyVal.int 42) := by native_decide

/-- `net_caller__eval` resolves cross-function calls via
    `interpWithCalls`. `pure_helper(21)` returns `42`, so
    `net_caller(21)` returns `42` (the doubled value). -/
example :
    (net_caller__eval (PyVal.int 21)).run = .ok (PyVal.int 42) := by native_decide

/-- The safe direction of the sub-permission lift: `Pure ⊆ Net` is
    decidable as `True`. This is what makes `Eff.liftSub`'s default
    `decide` proof go through. -/
example : Perms.sub Perms.none { net := true } := by decide

/-- The unsafe direction is decidably `False`. A `Net` computation
    cannot be silently lifted into a `Pure` context — the `decide`
    tactic refutes it, which is the soundness witness. -/
example : ¬ Perms.sub { net := true } Perms.none := by decide

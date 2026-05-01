/-!
# Effect-Indexed Monad for Monty Verification

This module defines the type-level machinery that makes "compilation IS
verification" work. A Monty function's effect annotation becomes a Lean
type: if the generated Lean code type-checks, the function's effects are
correct. If it doesn't, the Lean compiler error identifies the violation.

## Key Types

- `Perms`: a record of boolean flags for each effect capability
- `Eff p α`: an abstract computation that may use effects in `p` and returns `α`

## Key Axioms

- `Eff.pure`: lift a value into any effect context
- `Eff.bind`: sequence two computations with the same permissions
- `Eff.sub`: use a less-permissive computation in a more-permissive context

External functions are declared as axioms with specific `Perms` (the trust root).
Generated user code must type-check against its declared `Perms` — if it uses
an effect not in its permission set, the `Eff.sub` proof obligation is unprovable
and the file fails to compile.
-/

-- ============================================================================
-- Permission Flags
-- ============================================================================

/-- Permission flags tracking which effects a computation may produce.
    The four standard fields (`net`, `fs`, `env`, `time`) are bools for
    fast field-level comparisons. The `custom` list holds user-declared
    effect names beyond the standard taxonomy (e.g. `db`, `gpu`,
    `audit`) — declared in source via `# external: <name>
    <effect_name>` directives.

    The `custom` list is treated as a SET — `Perms.sub` checks subset
    membership rather than list equality. Convention: codegen-produced
    `custom` lists are sorted+deduped for canonicalisation. -/
structure Perms where
  net    : Bool := false
  fs     : Bool := false
  env    : Bool := false
  time   : Bool := false
  custom : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- No permissions — a pure computation. -/
def Perms.none : Perms := {}

/-- All permissions — an unrestricted computation. Used as the fixed
    effect set for opaque dynamic-dispatch axioms (`PyVal.callFn{0,1,2}`)
    so that any function calling them must itself be at `Perms.top`. This
    prevents the polymorphic-in-`p` callFn axioms from silently
    instantiating at `Perms.none` in a Pure context.

    `Perms.top` is a sentinel: any custom effect is automatically a
    subset of it via the `customSubset` rule below. The custom list of
    `Perms.top` is empty for canonical representation; the special-case
    in `Perms.sub` does the right thing. -/
def Perms.top : Perms :=
  { net := true, fs := true, env := true, time := true }

/-- True iff `p` is `Perms.top` (all four bools set). The custom list
    is ignored when checking topness — by convention `Perms.top` has
    an empty custom list and represents the maximal element. -/
def Perms.isTop (p : Perms) : Bool :=
  p.net && p.fs && p.env && p.time

/-- Subset relation: every permission enabled in `p₁` must also be
    enabled in `p₂`. The four standard fields use bool implication;
    the `custom` list uses subset membership. `Perms.top` (with all
    four bools set) absorbs every custom effect — that's the
    "anything goes" sentinel for dynamic dispatch. -/
def Perms.sub (p₁ p₂ : Perms) : Prop :=
  (p₁.net = true → p₂.net = true) ∧
  (p₁.fs = true → p₂.fs = true) ∧
  (p₁.env = true → p₂.env = true) ∧
  (p₁.time = true → p₂.time = true) ∧
  (p₂.isTop = true ∨ ∀ e, e ∈ p₁.custom → e ∈ p₂.custom)

instance (p₁ p₂ : Perms) : Decidable (p₁.sub p₂) := by
  unfold Perms.sub
  exact inferInstance

/-- Fuel-based sorted-dedup merge. Both inputs must already be sorted
    and deduped; the result is too. The fuel parameter is a structural
    `Nat` so the kernel unfolds this during reduction — critical for
    `permsOf` to discharge by `rfl` without `native_decide`. Using
    `List.mergeSort` (well-founded recursion) here blocks kernel
    reduction; this hand-written merge is the workaround. -/
def Perms.mergeCustomFuel : Nat → List String → List String → List String
  | 0,   _,       _       => []
  | _+1, [],      ys      => ys
  | _+1, xs,      []      => xs
  | n+1, x :: xs, y :: ys =>
    if x == y then x :: Perms.mergeCustomFuel n xs ys
    else if decide (x < y) then x :: Perms.mergeCustomFuel n xs (y :: ys)
    else y :: Perms.mergeCustomFuel n (x :: xs) ys

/-- Merge two sorted+deduped custom-effect lists. Fuel = total length,
    which is always sufficient because each recursive call drops at
    least one element. -/
def Perms.mergeCustom (xs ys : List String) : List String :=
  Perms.mergeCustomFuel (xs.length + ys.length) xs ys

/-- Pointwise union of two permission sets. Bool fields OR together;
    `custom` lists are merged via `Perms.mergeCustom`, which assumes
    both inputs are sorted+deduped (the invariant maintained by all
    callers — `Perms.none` and `Perms.top` have empty `custom` lists,
    and the codegen emits sorted+deduped literals).

    This replaces an earlier `List.mergeSort`-based implementation.
    `mergeSort` uses well-founded recursion and blocks kernel
    reduction, which prevented `permsOf` from discharging via `rfl`
    and forced per-function `native_decide` linkage theorems (Phase A
    v2). With the fuel-based merge, `permsOf env ast = literal` closes
    by `rfl` alone. -/
def Perms.union (p₁ p₂ : Perms) : Perms :=
  { net    := p₁.net || p₂.net
    fs     := p₁.fs || p₂.fs
    env    := p₁.env || p₂.env
    time   := p₁.time || p₂.time
    custom := Perms.mergeCustom p₁.custom p₂.custom }

-- ----------------------------------------------------------------------------
-- Union/sub lemmas (proven)
-- ----------------------------------------------------------------------------

private theorem mergeCustomFuel_mem_left {e : String} {xs ys : List String} {fuel : Nat}
    (hfuel : xs.length + ys.length ≤ fuel) (hmem : e ∈ xs)
    : e ∈ Perms.mergeCustomFuel fuel xs ys := by
  induction fuel generalizing xs ys with
  | zero =>
    have hlen : xs.length = 0 := by omega
    exact absurd (List.eq_nil_of_length_eq_zero hlen ▸ hmem) List.not_mem_nil
  | succ n ih =>
    cases xs with
    | nil => exact absurd hmem List.not_mem_nil
    | cons x xs' =>
      cases ys with
      | nil =>
        simp only [Perms.mergeCustomFuel]
        exact hmem
      | cons y ys' =>
        simp only [List.length_cons] at hfuel
        have hlen_ys : (y :: ys').length = ys'.length + 1 := List.length_cons
        have hlen_xs : (x :: xs').length = xs'.length + 1 := List.length_cons
        simp only [Perms.mergeCustomFuel]
        split
        · -- x == y
          apply List.mem_cons.mpr
          cases List.mem_cons.mp hmem with
          | inl h => left; exact h
          | inr h => right; exact ih (by omega) h
        · split
          · -- x < y
            apply List.mem_cons.mpr
            cases List.mem_cons.mp hmem with
            | inl h => left; exact h
            | inr h => right; exact ih (by simp only [List.length_cons]; omega) h
          · -- y < x
            apply List.mem_cons.mpr
            right; exact ih (by simp only [List.length_cons]; omega) hmem

private theorem mergeCustomFuel_mem_right {e : String} {xs ys : List String} {fuel : Nat}
    (hfuel : xs.length + ys.length ≤ fuel) (hmem : e ∈ ys)
    : e ∈ Perms.mergeCustomFuel fuel xs ys := by
  induction fuel generalizing xs ys with
  | zero =>
    have hlen : ys.length = 0 := by omega
    exact absurd (List.eq_nil_of_length_eq_zero hlen ▸ hmem) List.not_mem_nil
  | succ n ih =>
    cases xs with
    | nil => simp [Perms.mergeCustomFuel]; exact hmem
    | cons x xs' =>
      cases ys with
      | nil => exact absurd hmem List.not_mem_nil
      | cons y ys' =>
        simp only [List.length_cons] at hfuel
        have hlen_ys : (y :: ys').length = ys'.length + 1 := List.length_cons
        have hlen_xs : (x :: xs').length = xs'.length + 1 := List.length_cons
        simp only [Perms.mergeCustomFuel]
        split
        · -- x == y
          rename_i heq
          apply List.mem_cons.mpr
          cases List.mem_cons.mp hmem with
          | inl h =>
            left
            have := (beq_iff_eq (α := String)).mp heq
            rw [h]; exact this.symm
          | inr h => right; exact ih (by omega) h
        · split
          · -- x < y
            apply List.mem_cons.mpr
            right; exact ih (by simp only [List.length_cons]; omega) hmem
          · -- y < x
            apply List.mem_cons.mpr
            cases List.mem_cons.mp hmem with
            | inl h => left; exact h
            | inr h => right; exact ih (by simp only [List.length_cons]; omega) h

theorem Perms.subRefl (p : Perms) : p.sub p :=
  ⟨id, id, id, id, Or.inr fun _ h => h⟩

theorem Perms.subTrans {p q r : Perms} (h1 : p.sub q) (h2 : q.sub r) : p.sub r :=
  ⟨fun hp => h2.1 (h1.1 hp),
   fun hp => h2.2.1 (h1.2.1 hp),
   fun hp => h2.2.2.1 (h1.2.2.1 hp),
   fun hp => h2.2.2.2.1 (h1.2.2.2.1 hp),
   match h2.2.2.2.2 with
   | Or.inl htop => Or.inl htop
   | Or.inr h2c =>
     match h1.2.2.2.2 with
     | Or.inl htop =>
       Or.inl (by
         simp [Perms.isTop] at htop ⊢
         obtain ⟨⟨⟨hqn, hqf⟩, hqe⟩, hqt⟩ := htop
         exact ⟨⟨⟨h2.1 hqn, h2.2.1 hqf⟩, h2.2.2.1 hqe⟩, h2.2.2.2.1 hqt⟩)
     | Or.inr h1c => Or.inr fun e he => h2c e (h1c e he)⟩

theorem Perms.unionSubLeft (p q : Perms) : p.sub (p.union q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [Perms.union, h]
  · intro h; simp [Perms.union, h]
  · intro h; simp [Perms.union, h]
  · intro h; simp [Perms.union, h]
  · exact Or.inr fun e hmem => by
      simp only [Perms.union, Perms.mergeCustom]
      exact mergeCustomFuel_mem_left (Nat.le_refl _) hmem

theorem Perms.unionSubRight (p q : Perms) : q.sub (p.union q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [Perms.union, h]
  · intro h; simp [Perms.union, h]
  · intro h; simp [Perms.union, h]
  · intro h; simp [Perms.union, h]
  · exact Or.inr fun e hmem => by
      simp only [Perms.union, Perms.mergeCustom]
      exact mergeCustomFuel_mem_right (Nat.le_refl _) hmem

-- ============================================================================
-- Python built-in types (simplified representations)
-- ============================================================================

/-- Python values at the Lean level. We use a simple tagged union so that
    generated code has concrete types to work with. Defined before `Eff`
    so the effect monad can carry `PyVal` exception values in its
    `Except`-layered representation. -/
inductive PyVal where
  | none
  | bool : Bool → PyVal
  | int : Int → PyVal
  | float : Float → PyVal
  | str : String → PyVal
  | list : List PyVal → PyVal
  | tuple : List PyVal → PyVal
  | dict : List (PyVal × PyVal) → PyVal
  deriving Repr, Inhabited

-- ----------------------------------------------------------------------------
-- DecidableEq for PyVal
-- ----------------------------------------------------------------------------
--
-- `PyVal` carries `Float`, which is opaque to Lean and has no derivable
-- `DecidableEq` instance. We add one via a single axiom asserting that
-- `Float.toBits` is injective (i.e. two `Float`s with the same IEEE 754
-- bit pattern are propositionally equal). This is faithful to Lean's
-- runtime representation — `Float` is just a `UInt64` in disguise — and
-- it's the minimal extension to the trusted base needed to give the rest
-- of `PyVal` a `DecidableEq` instance.
--
-- Caveat: distinct NaN payloads are treated as distinct `Float` values,
-- which differs from IEEE `==` (where `NaN ≠ NaN`). For verification of
-- Monty programs this is the right call: we want propositional equality,
-- not floating-point equivalence.
--
-- Once `DecidableEq Float` exists, we hand-roll `DecidableEq PyVal` via
-- mutual recursion (Lean's `deriving DecidableEq` doesn't handle nested
-- recursive inductives like `PyVal.list : List PyVal → PyVal`). The
-- payoff is that `decide` and `native_decide` work as proof tactics on
-- `«__module__».run = .ok PyVal.none` propositions — the former for
-- programs that don't touch `Float`, the latter for those that do.

/-- Float bit-pattern injectivity. The only soundness assumption beyond
    Lean's core needed for `DecidableEq Float`. -/
axiom Float.toBits_inj : ∀ {a b : Float}, a.toBits = b.toBits → a = b

instance : DecidableEq Float := fun a b =>
  if h : a.toBits = b.toBits then
    .isTrue (Float.toBits_inj h)
  else
    .isFalse (fun heq => h (heq ▸ rfl))

mutual

/-- Decide propositional equality of two `PyVal`s. Mutually recursive
    with `decEqList` / `decEqDict` so the nested `List PyVal` /
    `List (PyVal × PyVal)` payloads have access to the recursive
    instance without going through Lean's typeclass resolution (which
    would loop on the not-yet-defined instance). -/
def PyVal.decEq : (a b : PyVal) → Decidable (a = b)
  | .none, .none => .isTrue rfl
  | .bool x, .bool y =>
      if h : x = y then .isTrue (by subst h; rfl)
      else .isFalse (fun he => h (PyVal.bool.inj he))
  | .int x, .int y =>
      if h : x = y then .isTrue (by subst h; rfl)
      else .isFalse (fun he => h (PyVal.int.inj he))
  | .float x, .float y =>
      if h : x = y then .isTrue (by subst h; rfl)
      else .isFalse (fun he => h (PyVal.float.inj he))
  | .str x, .str y =>
      if h : x = y then .isTrue (by subst h; rfl)
      else .isFalse (fun he => h (PyVal.str.inj he))
  | .list xs, .list ys =>
      match PyVal.decEqList xs ys with
      | .isTrue h => .isTrue (by subst h; rfl)
      | .isFalse h => .isFalse (fun he => h (PyVal.list.inj he))
  | .tuple xs, .tuple ys =>
      match PyVal.decEqList xs ys with
      | .isTrue h => .isTrue (by subst h; rfl)
      | .isFalse h => .isFalse (fun he => h (PyVal.tuple.inj he))
  | .dict xs, .dict ys =>
      match PyVal.decEqDict xs ys with
      | .isTrue h => .isTrue (by subst h; rfl)
      | .isFalse h => .isFalse (fun he => h (PyVal.dict.inj he))
  -- All cross-constructor pairs: distinct constructors are unequal,
  -- discharged by `cases h` (which uses `noConfusion`).
  | .none, .bool _ | .none, .int _ | .none, .float _ | .none, .str _
  | .none, .list _ | .none, .tuple _ | .none, .dict _
  | .bool _, .none | .bool _, .int _ | .bool _, .float _ | .bool _, .str _
  | .bool _, .list _ | .bool _, .tuple _ | .bool _, .dict _
  | .int _, .none | .int _, .bool _ | .int _, .float _ | .int _, .str _
  | .int _, .list _ | .int _, .tuple _ | .int _, .dict _
  | .float _, .none | .float _, .bool _ | .float _, .int _ | .float _, .str _
  | .float _, .list _ | .float _, .tuple _ | .float _, .dict _
  | .str _, .none | .str _, .bool _ | .str _, .int _ | .str _, .float _
  | .str _, .list _ | .str _, .tuple _ | .str _, .dict _
  | .list _, .none | .list _, .bool _ | .list _, .int _ | .list _, .float _
  | .list _, .str _ | .list _, .tuple _ | .list _, .dict _
  | .tuple _, .none | .tuple _, .bool _ | .tuple _, .int _ | .tuple _, .float _
  | .tuple _, .str _ | .tuple _, .list _ | .tuple _, .dict _
  | .dict _, .none | .dict _, .bool _ | .dict _, .int _ | .dict _, .float _
  | .dict _, .str _ | .dict _, .list _ | .dict _, .tuple _ =>
      .isFalse (fun h => by cases h)

/-- Decide equality on `List PyVal`. Hand-rolled rather than reusing
    `instDecidableEqList` because that instance would need
    `DecidableEq PyVal` already in scope. -/
def PyVal.decEqList : (xs ys : List PyVal) → Decidable (xs = ys)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun h => by cases h)
  | _ :: _, [] => .isFalse (fun h => by cases h)
  | x :: xs, y :: ys =>
      match PyVal.decEq x y with
      | .isFalse h => .isFalse (fun he => h (List.cons.inj he).1)
      | .isTrue hx =>
        match PyVal.decEqList xs ys with
        | .isFalse h => .isFalse (fun he => h (List.cons.inj he).2)
        | .isTrue hxs => .isTrue (by subst hx; subst hxs; rfl)

/-- Decide equality on `List (PyVal × PyVal)` (the dict payload). -/
def PyVal.decEqDict : (xs ys : List (PyVal × PyVal)) → Decidable (xs = ys)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun h => by cases h)
  | _ :: _, [] => .isFalse (fun h => by cases h)
  | (k1, v1) :: xs, (k2, v2) :: ys =>
      match PyVal.decEq k1 k2 with
      | .isFalse h => .isFalse (fun he => h (Prod.mk.inj (List.cons.inj he).1).1)
      | .isTrue hk =>
        match PyVal.decEq v1 v2 with
        | .isFalse h => .isFalse (fun he => h (Prod.mk.inj (List.cons.inj he).1).2)
        | .isTrue hv =>
          match PyVal.decEqDict xs ys with
          | .isFalse h => .isFalse (fun he => h (List.cons.inj he).2)
          | .isTrue hxs => .isTrue (by subst hk; subst hv; subst hxs; rfl)

end

instance : DecidableEq PyVal := PyVal.decEq

-- `Except` doesn't ship with a `DecidableEq` instance even when its
-- parameters have one, so derive it explicitly here. With this in place
-- `Decidable (Eff.run = .ok PyVal.none)` is synthesizable, which is the
-- shape of every "all top-level asserts pass" theorem we want users to
-- be able to dispatch with `decide` / `native_decide`.
deriving instance DecidableEq for Except

-- ============================================================================
-- Effect Monad (computable, Except-layered)
-- ============================================================================

/-- Non-local control flow carried by `Eff` at the value level. We
    distinguish two ways a computation can fail to return normally:

    - `.exception e` — a Python exception was raised, modeled as a `PyVal`
    - `.returned v`  — a `return` statement fired inside a nested block
      and needs to propagate up to the enclosing function boundary

    Distinguishing these is what makes `return` inside a `try`'s handler
    (or any non-tail position) actually exit the function. `tryCatch`
    catches `.exception` but **passes `.returned` through** unchanged, so
    a handler that does `return X` short-circuits all the way to
    `Eff.runFunction` at the function boundary, which converts `.returned`
    back to `.ok`. -/
inductive PyControl where
  | exception : PyVal → PyControl
  | returned  : PyVal → PyControl
  /-- A pending `break`. Caught by the enclosing `pyForEach` / `pyWhile`,
      which terminates the loop normally. Propagates through `bind` and
      `tryCatch` (only `.exception` is caught) until it hits a loop. -/
  | broke     : PyControl
  /-- A pending `continue`. Caught by the enclosing `pyForEach` /
      `pyWhile`, which skips to the next iteration. Same propagation
      semantics as `.broke`. -/
  | continued : PyControl
  deriving Repr, Inhabited, DecidableEq

/-- An effect-tracked computation that may either return a value or
    propagate non-local control (a raised exception or an early `return`).
    The `p` parameter records which effect capabilities the computation
    may exercise; `α` is the return type.

    Implementation: a phantom-typed `Except`-layered identity monad.
    `Eff p α` wraps `Except PyControl α` — `.ok x` is a normal flow,
    `.error (.exception e)` is a raised Python exception, and
    `.error (.returned v)` is an early `return v` waiting to be unwound at
    the enclosing function boundary by `Eff.runFunction`.

    The `structure` wrapper keeps `p` irreducible — `Eff { net := true } α`
    and `Eff {} α` remain distinct types, so widening permissions still
    requires going through `Eff.sub`. Generated code is **computable**:
    `#eval` works, `rfl`-style proofs work for pure (non-external)
    functions, and `try` / `raise` / non-tail `return` actually model
    Python's control flow rather than collapsing every block sequentially.

    User proofs typically compare against `.ok ...` because every
    generated function body is wrapped in `Eff.runFunction`, which
    converts `.returned v` to `.ok v` at the function boundary:
    ```lean
    example : (myFunc 5).run = .ok (PyVal.int 25) := by rfl
    ``` -/
structure Eff (p : Perms) (α : Type) where
  /-- The wrapped value. `.ok x` for normal return, `.error c` for raised
      exception or pending `return`. -/
  run : Except PyControl α

/-- Lift a pure value into any effect context. -/
def Eff.pure {p : Perms} {α : Type} (x : α) : Eff p α := ⟨.ok x⟩

/-- Sequence two computations with the same permissions. Short-circuits
    on **any** non-`ok` outcome: a raised exception or an early `return`
    both bypass the bound continuation and propagate outward.

    Implementation: pattern-match on the structure constructor directly,
    not via the `.run` projection. This makes `bind` reduce definitionally
    so user proofs can use `rfl` / `simp` on `do`-blocks involving `pure`,
    `raise`, `return`, and `tryCatch`. -/
def Eff.bind {p : Perms} {α β : Type} : Eff p α → (α → Eff p β) → Eff p β
  | ⟨.ok x⟩,    f => f x
  | ⟨.error c⟩, _ => ⟨.error c⟩

/-- Use a less-permissive computation in a more-permissive context. The
    proof obligation enforces effect tracking; the underlying `Except`
    value is rewrapped unchanged so control flow is preserved. -/
def Eff.sub {p₁ p₂ : Perms} {α : Type} (_h : p₁.sub p₂) : Eff p₁ α → Eff p₂ α
  | ⟨e⟩ => ⟨e⟩

/-- Codegen-friendly version of `Eff.sub`: the proof obligation is
    discharged by `decide` at the call site (default tactic argument), so
    generated code can write `Eff.liftSub (callee args)` whenever the
    callee's perms are a subset of the surrounding context's perms. If
    the perms relation doesn't hold, the `decide` fails and Lean rejects
    the file — which is the desired behaviour, since wrapping a more-
    permissive call in a less-permissive context would be unsound. -/
def Eff.liftSub {p₁ p₂ : Perms} {α : Type} (e : Eff p₁ α)
    (h : p₁.sub p₂ := by decide) : Eff p₂ α :=
  Eff.sub h e

/-- Union-bind: sequence an `Eff p α` with an `Eff q β` continuation,
    producing an `Eff (p.union q) β`. Internally lifts both sides to
    the union perm via `Perms.unionSubLeft` / `Perms.unionSubRight`,
    then delegates to `Eff.bind`.

    This is the key primitive that lets a dependently-typed `interp
    : (ast : EffAST) → Eff (permsOf ... ast) PyVal` thread subperm
    proofs structurally through `.seq` arms without needing to
    discharge `Perms.sub` at every recursive call site. The sub
    lemmas are axiomatised (see `Perms.unionSubLeft`) so this
    compiles without per-call proof obligations. -/
def Eff.bindSub {p q : Perms} {α β : Type}
    (e1 : Eff p α) (e2 : α → Eff q β) : Eff (p.union q) β :=
  let e1' : Eff (p.union q) α := Eff.sub (Perms.unionSubLeft p q) e1
  let e2' : α → Eff (p.union q) β := fun x => Eff.sub (Perms.unionSubRight p q) (e2 x)
  Eff.bind e1' e2'

/-- Raise a Python exception. Polymorphic in `α` and `p`. -/
def Eff.raise {p : Perms} {α : Type} (e : PyVal) : Eff p α :=
  ⟨.error (.exception e)⟩

/-- Issue an early `return v`. Polymorphic in `α` and `p`. The pending
    return propagates outward through every `bind` and through `tryCatch`
    (which only catches exceptions, not returns) until it hits the
    enclosing `Eff.runFunction` at the function boundary. -/
def Eff.return {p : Perms} {α : Type} (v : PyVal) : Eff p α :=
  ⟨.error (.returned v)⟩

/-- Catch a raised exception. If `body` returns normally, its result is
    returned unchanged; if it raises, `handler` is invoked with the
    exception value. **Pending control flow other than exceptions is
    passed through unchanged** — a `return` / `break` / `continue`
    inside `body` (or inside `handler`) does not get caught here, so
    it propagates to the enclosing function boundary or loop. -/
def Eff.tryCatch {p : Perms} {α : Type}
    : Eff p α → (PyVal → Eff p α) → Eff p α
  | ⟨.ok x⟩,                  _       => ⟨.ok x⟩
  | ⟨.error (.exception e)⟩,  handler => handler e
  | ⟨.error (.returned v)⟩,   _       => ⟨.error (.returned v)⟩
  | ⟨.error .broke⟩,          _       => ⟨.error .broke⟩
  | ⟨.error .continued⟩,      _       => ⟨.error .continued⟩

/-- Run `cleanup` after `body`, whether `body` finished normally, raised,
    or fired an early `return`. If `cleanup` itself raises or returns,
    that outcome masks the body's (matching Python's `try/finally`). -/
def Eff.tryFinally {p : Perms} {α : Type}
    : Eff p α → Eff p Unit → Eff p α
  | ⟨.ok x⟩,    ⟨.ok _⟩    => ⟨.ok x⟩
  | ⟨.ok _⟩,    ⟨.error c⟩ => ⟨.error c⟩
  | ⟨.error c⟩, ⟨.ok _⟩    => ⟨.error c⟩
  | ⟨.error _⟩, ⟨.error c⟩ => ⟨.error c⟩

/-- Function boundary: evaluate `body` and convert a pending `return v`
    back into a normal `.ok v`. Raised exceptions still propagate as
    `.error (.exception e)`, and a body that finished normally with
    `.ok x` is left untouched.

    Codegen wraps every generated function body in `Eff.runFunction` so
    that an early `return` inside any nested block (an `if`, a handler,
    a `for`-body) actually exits the *function*, not just its immediately
    enclosing block. -/
def Eff.runFunction {p : Perms} : Eff p PyVal → Eff p PyVal
  | ⟨.ok x⟩                 => ⟨.ok x⟩
  | ⟨.error (.exception e)⟩ => ⟨.error (.exception e)⟩
  | ⟨.error (.returned v)⟩  => ⟨.ok v⟩
  -- A `break` / `continue` that escapes a function (i.e. wasn't caught
  -- by an enclosing loop) is a SyntaxError in Python — it should never
  -- happen in well-formed source. We collapse to `.ok PyVal.none` so the
  -- file still type-checks defensively.
  | ⟨.error .broke⟩         => ⟨.ok .none⟩
  | ⟨.error .continued⟩     => ⟨.ok .none⟩

/-- Issue a pending `break`. Caught by the nearest enclosing
    `pyForEach` / `pyWhile`, which terminates the loop. -/
def Eff.break {p : Perms} {α : Type} : Eff p α :=
  ⟨.error .broke⟩

/-- Issue a pending `continue`. Caught by the nearest enclosing
    `pyForEach` / `pyWhile`, which skips to the next iteration. -/
def Eff.continue {p : Perms} {α : Type} : Eff p α :=
  ⟨.error .continued⟩

-- Monad instance so we can use `do` notation with `Eff p`. The `bind`
-- defined above already short-circuits on `.error`, so `do let x ← m; ...`
-- behaves like Python's "raise propagates out unless caught".
instance : Monad (Eff p) where
  pure := Eff.pure
  bind := Eff.bind

/-- Lift a less-permissive computation into `Eff Perms.top`. Used by
    codegen in do-blocks whose surrounding context has been widened to
    `Perms.top` (because the body does dynamic dispatch via
    `PyVal.callFn`) so that bindings to lower-permission helpers like
    `let _tmp ← Eff.liftToTop (some_pure_helper x)` still type-check.
    The lift is sound because `Perms.top` permits every effect, and
    `Eff` carries no runtime data tied to `p` — the index is purely
    phantom, so the underlying `Except PyControl α` is rewrapped
    unchanged. A `MonadLift` instance would be cleaner, but Lean
    rejects it because the source monad's `p` index can't be inferred
    from the target `Eff Perms.top` alone (semiOutParam restriction).

    The `Perms.top` target is hardcoded so codegen can emit
    `Eff.liftToTop (callee args)` without leaving a metavariable for
    Lean to infer — important inside nested lambda bodies (e.g. lambdas
    in `pyListComp`) where the surrounding type isn't pinned. For
    arbitrary intermediate perms, use `Eff.liftSub`. -/
def Eff.liftToTop {p : Perms} {α : Type} : Eff p α → Eff Perms.top α
  | ⟨e⟩ => ⟨e⟩

-- ============================================================================
-- Python operations
-- ============================================================================
--
-- These are the runtime semantics that generated Lean code calls into.
-- They aim for "honest enough that propositions about Monty programs are
-- meaningful" — not full CPython fidelity. Where Python is dynamic and
-- our `PyVal` doesn't carry enough information to compute the right
-- result, we fall back to the left operand or `PyVal.none`. The fallback
-- is *deliberate*: it produces a well-defined value so theorems can be
-- stated, while still being obviously wrong if the user proves something
-- depending on the fallback path (which would tip them off).
--
-- All functions are total and computable, so generated code can be
-- `#eval`-ed and equational proofs can use `rfl` / `simp` / `decide`.

-- ----------------------------------------------------------------------------
-- Truthiness, length, indexing
-- ----------------------------------------------------------------------------

/-- Python truthiness: maps any `PyVal` to `Bool` according to Python's
    rules. Empty containers and zero are falsy; everything else is truthy. -/
def pyTruthy : PyVal → Bool
  | .none => false
  | .bool b => b
  | .int n => n != 0
  | .float f => f != 0.0
  | .str s => !s.isEmpty
  | .list l => !l.isEmpty
  | .tuple l => !l.isEmpty
  | .dict d => !d.isEmpty

/-- Python `len()`. Defined on strings, lists, tuples, and dicts. -/
def pyLen : PyVal → PyVal
  | .str s => .int s.length
  | .list l => .int l.length
  | .tuple l => .int l.length
  | .dict d => .int d.length
  | _ => .int 0

/-- Subscript / `obj[index]`. Bounds-checked; out-of-range returns `.none`. -/
def pyIndex : PyVal → PyVal → PyVal
  | .list l, .int i => match l[i.toNat]? with | some v => v | none => .none
  | .tuple l, .int i => match l[i.toNat]? with | some v => v | none => .none
  | .str s, .int i =>
    -- Single-character substring at byte position `i`. We use the
    -- "drop i, take 1" idiom to avoid String.Pos arithmetic, which
    -- changed shape between Lean releases.
    let rest := (s.toList.drop i.toNat).take 1
    .str (String.mk rest)
  | .dict d, k =>
    -- Linear scan; sufficient for verification, not for performance.
    match d.find? (fun (dk, _) => decide (pyEqRaw dk k)) with
    | some (_, v) => v
    | none => .none
  | _, _ => .none
where
  /-- Bare boolean equality on `PyVal` for use in dict lookup. The
      user-visible `pyEq` returns a `PyVal.bool`; this returns a `Bool` so
      it's usable in `decide`. -/
  pyEqRaw : PyVal → PyVal → Bool
    | .none, .none => true
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .str a, .str b => a == b
    | _, _ => false

/-- Slice an indexable container. Used by codegen to lower
    `obj[start:stop:step]` to a real list/tuple/string slice rather
    than the previous `pyIndex obj PyVal.none` collapse. `start`, `stop`,
    and `step` are `PyVal.int` or `PyVal.none`; missing entries default
    to Python's defaults (start=0 for positive step, len-1 for negative;
    stop=len for positive step, -1 for negative; step=1). Negative
    indices wrap from the end. Step values other than ±1 are supported
    via stride accumulation. -/
def pySlice (obj start stop step : PyVal) : PyVal :=
  let stepN : Int := match step with | .int i => i | _ => 1
  let normalize (i : Int) (n : Int) : Int :=
    if i < 0 then max 0 (i + n) else min n i
  let buildIndices (n : Int) : List Nat :=
    let s : Int := match start with
      | .int i => normalize i n
      | _ => if stepN > 0 then 0 else n - 1
    let e : Int := match stop with
      | .int i => normalize i n
      | _ => if stepN > 0 then n else -1
    let rec go (cur : Int) (fuel : Nat) (acc : List Nat) : List Nat :=
      match fuel with
      | 0 => acc.reverse
      | f + 1 =>
        let cont :=
          if stepN > 0 then cur < e
          else if stepN < 0 then cur > e
          else false
        if cont && cur >= 0 && cur < n then
          go (cur + stepN) f (cur.toNat :: acc)
        else acc.reverse
    go s n.toNat []
  match obj with
  | .list xs =>
    let idxs := buildIndices xs.length
    .list (idxs.filterMap (fun i => xs[i]?))
  | .tuple xs =>
    let idxs := buildIndices xs.length
    .tuple (idxs.filterMap (fun i => xs[i]?))
  | .str s =>
    let chars := s.toList
    let idxs := buildIndices chars.length
    .str (String.mk (idxs.filterMap (fun i => chars[i]?)))
  | _ => .none

-- ----------------------------------------------------------------------------
-- Binary arithmetic & bitwise operators
-- ----------------------------------------------------------------------------

/-- Addition. Numeric addition on int/float/bool, concatenation on
    str/list/tuple. Falls back to the left operand for mismatched types. -/
def pyAdd : PyVal → PyVal → PyVal
  | .int a, .int b => .int (a + b)
  | .float a, .float b => .float (a + b)
  | .int a, .float b => .float ((Float.ofInt a) + b)
  | .float a, .int b => .float (a + (Float.ofInt b))
  | .bool a, .bool b => .int ((if a then 1 else 0) + (if b then 1 else 0))
  | .str a, .str b => .str (a ++ b)
  | .list a, .list b => .list (a ++ b)
  | .tuple a, .tuple b => .tuple (a ++ b)
  | a, _ => a

/-- Subtraction. -/
def pySub : PyVal → PyVal → PyVal
  | .int a, .int b => .int (a - b)
  | .float a, .float b => .float (a - b)
  | .int a, .float b => .float ((Float.ofInt a) - b)
  | .float a, .int b => .float (a - (Float.ofInt b))
  | a, _ => a

/-- Multiplication. Numeric mul, plus Python's `"x" * 3` and `[1] * 3` reps. -/
def pyMul : PyVal → PyVal → PyVal
  | .int a, .int b => .int (a * b)
  | .float a, .float b => .float (a * b)
  | .int a, .float b => .float ((Float.ofInt a) * b)
  | .float a, .int b => .float (a * (Float.ofInt b))
  | .str s, .int n =>
    -- String.replicate may not exist in this Lean version; use a fold.
    .str ((List.replicate n.toNat s).foldl (· ++ ·) "")
  | .int n, .str s =>
    .str ((List.replicate n.toNat s).foldl (· ++ ·) "")
  | .list l, .int n => .list (List.replicate n.toNat l).flatten
  | .int n, .list l => .list (List.replicate n.toNat l).flatten
  | a, _ => a

/-- True division (Python `/`): always returns a float. -/
def pyDiv : PyVal → PyVal → PyVal
  | .int a, .int b => if b == 0 then .none else .float ((Float.ofInt a) / (Float.ofInt b))
  | .float a, .float b => if b == 0.0 then .none else .float (a / b)
  | .int a, .float b => if b == 0.0 then .none else .float ((Float.ofInt a) / b)
  | .float a, .int b => if b == 0 then .none else .float (a / (Float.ofInt b))
  | a, _ => a

/-- Floor division (Python `//`). For negatives this rounds toward
    negative infinity, matching Python (and Lean's `Int.div` doesn't,
    so we adjust). -/
def pyFloorDiv : PyVal → PyVal → PyVal
  | .int a, .int b =>
    if b == 0 then .none
    else
      -- Python: a // b rounds toward -infinity. Lean's `/` truncates toward 0.
      let q := a / b
      let r := a % b
      if (r != 0) && ((r < 0) != (b < 0)) then .int (q - 1) else .int q
  | .float a, .float b => if b == 0.0 then .none else .float (a / b).floor
  | a, _ => a

/-- Modulo (Python `%`). Sign matches the divisor (Python convention). -/
def pyMod : PyVal → PyVal → PyVal
  | .int a, .int b =>
    if b == 0 then .none
    else
      let r := a % b
      if (r != 0) && ((r < 0) != (b < 0)) then .int (r + b) else .int r
  | a, _ => a

/-- Power (Python `**`). Only defined for non-negative integer exponents
    here; negative exponents would return a float in Python and we don't
    bother with that case. -/
def pyPow : PyVal → PyVal → PyVal
  | .int a, .int b => if b < 0 then .none else .int (a ^ b.toNat)
  | a, _ => a

/-- Matrix multiplication (Python `@`). Not modeled — returns left operand. -/
def pyMatMult : PyVal → PyVal → PyVal := fun a _ => a

/-- Bitwise OR. Defined for non-negative integers via `Nat.lor`; falls back
    to the left operand for negative inputs. -/
def pyBitOr : PyVal → PyVal → PyVal
  | .int a, .int b =>
    if a >= 0 && b >= 0 then .int (Int.ofNat (a.toNat ||| b.toNat))
    else .int a
  | .bool a, .bool b => .bool (a || b)
  | a, _ => a

/-- Bitwise AND. -/
def pyBitAnd : PyVal → PyVal → PyVal
  | .int a, .int b =>
    if a >= 0 && b >= 0 then .int (Int.ofNat (a.toNat &&& b.toNat))
    else .int a
  | .bool a, .bool b => .bool (a && b)
  | a, _ => a

/-- Bitwise XOR. -/
def pyBitXor : PyVal → PyVal → PyVal
  | .int a, .int b =>
    if a >= 0 && b >= 0 then .int (Int.ofNat (a.toNat ^^^ b.toNat))
    else .int a
  | .bool a, .bool b => .bool (a != b)
  | a, _ => a

/-- Left shift. -/
def pyLShift : PyVal → PyVal → PyVal
  | .int a, .int b => if b < 0 then .none else .int (a <<< b.toNat)
  | a, _ => a

/-- Right shift. -/
def pyRShift : PyVal → PyVal → PyVal
  | .int a, .int b => if b < 0 then .none else .int (a >>> b.toNat)
  | a, _ => a

/-- Logical AND with Python's short-circuit return value: returns `a` if
    `a` is falsy, else `b`. -/
def pyAnd : PyVal → PyVal → PyVal := fun a b => if pyTruthy a then b else a

/-- Logical OR: returns `a` if truthy, else `b`. -/
def pyOr : PyVal → PyVal → PyVal := fun a b => if pyTruthy a then a else b

-- ----------------------------------------------------------------------------
-- Comparison operators (all return PyVal.bool)
-- ----------------------------------------------------------------------------

/-- Equality. Defined cross-type for the common cases; mismatched types
    are unequal except for `int`/`float`/`bool` numeric coercion. -/
def pyEq : PyVal → PyVal → PyVal
  | .none, .none => .bool true
  | .bool a, .bool b => .bool (a == b)
  | .int a, .int b => .bool (a == b)
  | .float a, .float b => .bool (a == b)
  | .str a, .str b => .bool (a == b)
  | .int a, .bool b => .bool (a == (if b then 1 else 0))
  | .bool a, .int b => .bool ((if a then 1 else 0) == b)
  | .int a, .float b => .bool ((Float.ofInt a) == b)
  | .float a, .int b => .bool (a == (Float.ofInt b))
  -- Compound types compare structurally via the hand-written
  -- `DecidableEq PyVal`. This makes `assert [1, 2] == [1, 2]` reduce
  -- to `pyEq (.list [..]) (.list [..])  →  .bool true` so proofs of
  -- `«__module__».run = .ok PyVal.none` go through by `decide` /
  -- `native_decide` (and by `rfl` for files that don't touch `Float`).
  | .list xs, .list ys => .bool (decide (xs = ys))
  | .tuple xs, .tuple ys => .bool (decide (xs = ys))
  | .dict xs, .dict ys => .bool (decide (xs = ys))
  | _, _ => .bool false

/-- Inequality. -/
def pyNotEq (a b : PyVal) : PyVal :=
  match pyEq a b with | .bool x => .bool (!x) | _ => .bool true

/-- Less-than. Numeric and lexicographic string comparison. -/
def pyLt : PyVal → PyVal → PyVal
  | .int a, .int b => .bool (a < b)
  | .float a, .float b => .bool (a < b)
  | .int a, .float b => .bool ((Float.ofInt a) < b)
  | .float a, .int b => .bool (a < (Float.ofInt b))
  | .str a, .str b => .bool (a < b)
  | _, _ => .bool false

/-- Less-than-or-equal. -/
def pyLe (a b : PyVal) : PyVal :=
  match pyLt a b, pyEq a b with
  | .bool x, .bool y => .bool (x || y)
  | _, _ => .bool false

/-- Greater-than: just `pyLt b a`. -/
def pyGt (a b : PyVal) : PyVal := pyLt b a

/-- Greater-than-or-equal. -/
def pyGe (a b : PyVal) : PyVal :=
  match pyLt b a, pyEq a b with
  | .bool x, .bool y => .bool (x || y)
  | _, _ => .bool false

/-- `is` — Python identity. We don't model object identity, so we treat
    it as value equality for atoms (None, bool, small int) and `false`
    otherwise. This is a deliberate over-approximation. -/
def pyIs : PyVal → PyVal → PyVal
  | .none, .none => .bool true
  | .bool a, .bool b => .bool (a == b)
  | _, _ => .bool false

/-- `is not`. -/
def pyIsNot (a b : PyVal) : PyVal :=
  match pyIs a b with | .bool x => .bool (!x) | _ => .bool true

/-- `in` — membership. Implemented for str, list, tuple, dict (key check). -/
def pyIn : PyVal → PyVal → PyVal
  | needle, .list l =>
    .bool (l.any fun x => match pyEq x needle with | .bool b => b | _ => false)
  | needle, .tuple l =>
    .bool (l.any fun x => match pyEq x needle with | .bool b => b | _ => false)
  | .str s, .str hay =>
    -- "needle in haystack": empty needle always matches; otherwise check
    -- whether splitOn finds at least one occurrence (i.e. produces 2+
    -- pieces). Avoids depending on `String.containsSubstr`, which doesn't
    -- exist in older Lean.
    .bool (s.isEmpty || (hay.splitOn s).length >= 2)
  | needle, .dict d =>
    .bool (d.any fun (k, _) => match pyEq k needle with | .bool b => b | _ => false)
  | _, _ => .bool false

/-- `not in`. -/
def pyNotIn (a b : PyVal) : PyVal :=
  match pyIn a b with | .bool x => .bool (!x) | _ => .bool true

/-- Optimised `x % m == val` from Monty's `modEq` comparison operator.
    Monty's IR shape is `CmpOp { left: x, op: ModEq(val), right: m }`,
    so the comparison value is carried by the operator and the modulus
    is the right operand. -/
def pyModEq (val : Int) (m : PyVal) : PyVal → PyVal
  | .int a =>
    match m with
    | .int mInt => if mInt == 0 then .bool false else .bool (a % mInt == val)
    | _ => .bool false
  | _ => .bool false

-- ----------------------------------------------------------------------------
-- Unary operators
-- ----------------------------------------------------------------------------

/-- Unary negation. -/
def pyNeg : PyVal → PyVal
  | .int a => .int (-a)
  | .float a => .float (-a)
  | .bool a => .int (if a then -1 else 0)
  | a => a

/-- Unary plus. Numeric identity; bool → int. -/
def pyPos : PyVal → PyVal
  | .int a => .int a
  | .float a => .float a
  | .bool a => .int (if a then 1 else 0)
  | a => a

/-- Bitwise invert (Python `~x`): `-x - 1`. -/
def pyInvert : PyVal → PyVal
  | .int a => .int (-a - 1)
  | .bool a => .int (if a then -2 else -1)
  | a => a

/-- Logical not. -/
def pyNot (a : PyVal) : PyVal := .bool (!pyTruthy a)

-- ============================================================================
-- Lift helper (for generated code)
-- ============================================================================

/-- Convenience: lift a pure value into an effectful context.
    Generated code uses this when calling a pure function from an effectful one. -/
theorem Perms.none_sub (p : Perms) : Perms.none.sub p :=
  ⟨fun h => by simp [Perms.none] at h,
   fun h => by simp [Perms.none] at h,
   fun h => by simp [Perms.none] at h,
   fun h => by simp [Perms.none] at h,
   Or.inr (fun e h => by simp [Perms.none] at h)⟩

/-- Lift a pure computation into any effect context. -/
def liftPure {p : Perms} (ma : Eff Perms.none α) : Eff p α :=
  Eff.sub (Perms.none_sub p) ma

-- ============================================================================
-- String formatting (for f-strings)
-- ============================================================================

-- pyToStr converts a `PyVal` to a Lean `String` for use in f-string
-- interpolation. Mirrors Python's `str()` for the common cases —
-- int/float/bool/str map directly; collections use a simple `repr`-style
-- rendering. **Not** marked `partial` so that `rfl`/`simp` can reduce
-- f-string equations during proof. The mutual block lets the helpers be
-- defined alongside without colliding with each other.
mutual
  /-- Convert a `PyVal` to a Lean `String` for f-string interpolation. -/
  def pyToStr : PyVal → String
    | .none => "None"
    | .bool true => "True"
    | .bool false => "False"
    | .int n => toString n
    | .float f => toString f
    | .str s => s
    | .list xs => "[" ++ pyToStrList xs ++ "]"
    | .tuple xs => "(" ++ pyToStrList xs ++ ")"
    | .dict d => "{" ++ pyToStrDict d ++ "}"

  /-- Comma-join a list of PyVals as their string forms. -/
  def pyToStrList : List PyVal → String
    | [] => ""
    | [x] => pyToStr x
    | x :: rest => pyToStr x ++ ", " ++ pyToStrList rest

  /-- Comma-join a list of (key, value) pairs as `k: v` strings. -/
  def pyToStrDict : List (PyVal × PyVal) → String
    | [] => ""
    | [(k, v)] => pyToStr k ++ ": " ++ pyToStr v
    | (k, v) :: rest => pyToStr k ++ ": " ++ pyToStr v ++ ", " ++ pyToStrDict rest
end

/-- Build a `PyVal.str` by concatenating a list of pieces. Used by codegen
    to materialize an f-string after each interpolated value has been
    evaluated and converted via `pyToStr`. -/
def pyStrJoin (parts : List String) : PyVal :=
  .str (String.intercalate "" parts)

-- ============================================================================
-- Iteration
-- ============================================================================

/-- Iterate the body once for each element of `iter`. The body's effect
    set propagates into the result via `Eff p Unit`, so a `for` loop
    inside a `Pure` function whose body calls a `Net` external becomes a
    `Eff { net := true } Unit` and fails to type-check.

    Iteration shape:
    - `list xs` / `tuple xs` — iterate elements in order
    - `str s`                — iterate single-character substrings
    - `dict d`               — iterate keys (matching Python's `for k in d`)
    - anything else          — no iterations (silent no-op, mirroring an
      empty iterable)

    Control flow inside the body:
    - `Eff.break`     — terminates the loop normally (this iteration's
      body run is skipped, like Python's `break`).
    - `Eff.continue`  — skips to the next iteration.
    - `Eff.return v`  — propagates outward to the enclosing function
      boundary unchanged.
    - `Eff.raise e`   — propagates outward unchanged.

    `pyForEach` is fully computable: a pure `for` loop can be `#eval`'d
    and equational proofs about loop-accumulators can use `simp` /
    `decide` once the loop has been unfolded. -/
def pyForEachList {p : Perms} : List PyVal → (PyVal → Eff p Unit) → Eff p Unit
  | [],       _ => ⟨.ok ()⟩
  | x :: xs,  f =>
    match f x with
    | ⟨.ok _⟩              => pyForEachList xs f
    | ⟨.error .broke⟩      => ⟨.ok ()⟩            -- catch break: exit loop
    | ⟨.error .continued⟩  => pyForEachList xs f  -- catch continue: next iter
    | ⟨.error c⟩           => ⟨.error c⟩           -- exception/return: propagate

def pyForEach {p : Perms} : PyVal → (PyVal → Eff p Unit) → Eff p Unit
  | .list xs, f => pyForEachList xs f
  | .tuple xs, f => pyForEachList xs f
  | .str s, f =>
    -- Walk each Unicode character, wrapped as a single-char PyVal.str.
    pyForEachList (s.toList.map fun c => .str (String.mk [c])) f
  | .dict d, f => pyForEachList (d.map (·.1)) f
  | _, _ => pure ()

/-- P1: fold-style for-loop that threads accumulator state through
    each iteration. Used when the loop body mutates variables from
    the enclosing scope (e.g. `results.append(x)` inside a for-loop).
    The accumulator `σ` holds the live mutated variables, packed as
    a single `PyVal` (or `PyVal.tuple` for multiple).

    The loop body `f acc item` receives the current accumulator and
    the loop variable, and returns the updated accumulator. Break
    returns the current accumulator; continue skips to the next
    iteration without updating; exceptions and returns propagate. -/
def pyForFoldList {p : Perms} : List PyVal → PyVal → (PyVal → PyVal → Eff p PyVal) → Eff p PyVal
  | [],      acc, _ => pure acc
  | x :: xs, acc, f =>
    match f acc x with
    | ⟨.ok acc'⟩          => pyForFoldList xs acc' f
    | ⟨.error .broke⟩     => pure acc    -- break: exit with current acc
    | ⟨.error .continued⟩ => pyForFoldList xs acc f  -- continue: keep acc
    | ⟨.error c⟩          => ⟨.error c⟩  -- exception/return: propagate

def pyForFold {p : Perms} : PyVal → PyVal → (PyVal → PyVal → Eff p PyVal) → Eff p PyVal
  | .list xs, acc, f => pyForFoldList xs acc f
  | .tuple xs, acc, f => pyForFoldList xs acc f
  | .str s, acc, f =>
    pyForFoldList (s.toList.map fun c => .str (String.mk [c])) acc f
  | .dict d, acc, f => pyForFoldList (d.map (·.1)) acc f
  | _, acc, _ => pure acc

/-- Iterate over a `PyVal`'s elements, returning the underlying Lean
    `List PyVal`. Used by the comprehension helpers below to drive
    iteration without going through `Eff`. -/
def pyElems : PyVal → List PyVal
  | .list xs => xs
  | .tuple xs => xs
  | .str s => s.toList.map fun c => .str (String.mk [c])
  | .dict d => d.map (·.1)
  | _ => []

-- ----------------------------------------------------------------------------
-- Built-in functions
-- ----------------------------------------------------------------------------
--
-- These mirror Python's `len`, `abs`, `str`, `int`, `min`, `max`, `sum`,
-- `divmod`, `hex`, `bin`, `oct`, `chr`, `ord`, `round`, `sorted`, `bool`,
-- `float`, `repr`, `hash`, `id`, `type`. Each is total and computable, so
-- proofs about builtins reduce by `rfl` / `decide` / `native_decide`.
-- Unsupported inputs map to `.none` (matching the project-wide
-- "produce a well-defined value rather than crashing" convention).
-- They live here, after `pyToStr` and `pyElems`, because several depend
-- on those.
--
-- Codegen dispatches `.call (.builtin "Len") (.simple [x])` to `pyLen x`,
-- etc., via the `builtinUnary` / `builtinBinary` tables in `Codegen.lean`.

/-- Python `abs(x)`. -/
def pyAbs : PyVal → PyVal
  | .int a => .int a.natAbs
  | .float a => .float a.abs
  | .bool a => .int (if a then 1 else 0)
  | _ => .none

/-- Python `bool(x)`. Always succeeds — wraps `pyTruthy`. -/
def pyBool (a : PyVal) : PyVal := .bool (pyTruthy a)

/-- Python `int(x)`. Numeric coercion (float→int truncates toward zero
    like Python 3); strings are parsed via `String.toInt?`, returning
    `.none` on failure. -/
def pyInt : PyVal → PyVal
  | .int a => .int a
  | .bool a => .int (if a then 1 else 0)
  | .float a => .int a.toInt64.toInt
  | .str s => match s.toInt? with | some n => .int n | none => .none
  | _ => .none

/-- Python `float(x)`. Int and bool coerce; floats pass through;
    everything else returns `.none`. -/
def pyFloat : PyVal → PyVal
  | .float a => .float a
  | .int a => .float (Float.ofInt a)
  | .bool a => .float (if a then 1.0 else 0.0)
  | _ => .none

/-- Python `str(x)`. Wraps `pyToStr` into a `PyVal.str`. -/
def pyStr (a : PyVal) : PyVal := .str (pyToStr a)

/-- Python `repr(x)`. We use the same rendering as `str()` for the common
    cases, with single-quotes around string values. -/
def pyRepr : PyVal → PyVal
  | .str s => .str ("'" ++ s ++ "'")
  | a => .str (pyToStr a)

/-- Python `hash(x)`. We don't model object hashing; every value hashes
    to 0. Identity assertions like `hash(a) == hash(b)` would always
    pass, but most realistic uses (`d[key]`) go through `pyIndex`, which
    doesn't consult the hash. -/
def pyHash (_ : PyVal) : PyVal := .int 0

/-- Python `id(x)`. Same opaque-zero placeholder as `hash`. -/
def pyId (_ : PyVal) : PyVal := .int 0

/-- Python `type(x).__name__`. Returns a string tag for the value's
    runtime type — good enough for `assert type(x).__name__ == "int"`
    style checks. -/
def pyType : PyVal → PyVal
  | .none => .str "NoneType"
  | .bool _ => .str "bool"
  | .int _ => .str "int"
  | .float _ => .str "float"
  | .str _ => .str "str"
  | .list _ => .str "list"
  | .tuple _ => .str "tuple"
  | .dict _ => .str "dict"

/-- Python `min(a, b)`. -/
def pyMin2 (a b : PyVal) : PyVal :=
  match pyLt a b with | .bool true => a | _ => b

/-- Python `max(a, b)`. -/
def pyMax2 (a b : PyVal) : PyVal :=
  match pyLt a b with | .bool true => b | _ => a

/-- `min(xs)` over a Lean list. Empty list returns `.none` (Python raises
    `ValueError`; we don't, since we want totality). -/
def pyMinList : List PyVal → PyVal
  | [] => .none
  | [x] => x
  | x :: xs => pyMin2 x (pyMinList xs)

/-- `max(xs)` over a Lean list. -/
def pyMaxList : List PyVal → PyVal
  | [] => .none
  | [x] => x
  | x :: xs => pyMax2 x (pyMaxList xs)

/-- Python `min(iter)` — single-iterable form. -/
def pyMinIter (a : PyVal) : PyVal := pyMinList (pyElems a)

/-- Python `max(iter)` — single-iterable form. -/
def pyMaxIter (a : PyVal) : PyVal := pyMaxList (pyElems a)

/-- `sum(xs)` over a Lean list, starting from `0`. -/
def pySumList : List PyVal → PyVal
  | [] => .int 0
  | x :: xs => pyAdd x (pySumList xs)

/-- Python `sum(iter)`. Matches Python: `sum([])` is `0`. -/
def pySumIter (a : PyVal) : PyVal := pySumList (pyElems a)

/-- Python `divmod(a, b)`. Returns `(a // b, a % b)` as a tuple, or
    `.none` for the divide-by-zero case. -/
def pyDivmod (a b : PyVal) : PyVal :=
  match pyFloorDiv a b, pyMod a b with
  | .none, _ => .none
  | _, .none => .none
  | q, r => .tuple [q, r]

/-- Python `chr(n)`. -/
def pyChr : PyVal → PyVal
  | .int n =>
    if 0 ≤ n ∧ n ≤ 0x10FFFF then
      .str (String.mk [Char.ofNat n.toNat])
    else .none
  | _ => .none

/-- Python `ord(c)`. Single-character string → codepoint. -/
def pyOrd : PyVal → PyVal
  | .str s =>
    match s.toList with
    | [c] => .int (Int.ofNat c.toNat)
    | _ => .none
  | _ => .none

/-- Python `hex(n)`. Lower-case hex with `0x` prefix; negatives get a
    leading `-` (matching CPython). -/
def pyHex : PyVal → PyVal
  | .int n =>
    if n < 0 then .str ("-0x" ++ String.mk (Nat.toDigits 16 n.natAbs))
    else .str ("0x" ++ String.mk (Nat.toDigits 16 n.toNat))
  | _ => .none

/-- Python `bin(n)`. Binary with `0b` prefix. -/
def pyBin : PyVal → PyVal
  | .int n =>
    if n < 0 then .str ("-0b" ++ String.mk (Nat.toDigits 2 n.natAbs))
    else .str ("0b" ++ String.mk (Nat.toDigits 2 n.toNat))
  | _ => .none

/-- Python `oct(n)`. Octal with `0o` prefix. -/
def pyOct : PyVal → PyVal
  | .int n =>
    if n < 0 then .str ("-0o" ++ String.mk (Nat.toDigits 8 n.natAbs))
    else .str ("0o" ++ String.mk (Nat.toDigits 8 n.toNat))
  | _ => .none

/-- Python `round(x)` (one-arg form). Float→int rounding via
    `Float.toInt64`. Int passes through; bool coerces. -/
def pyRound : PyVal → PyVal
  | .int a => .int a
  | .bool a => .int (if a then 1 else 0)
  | .float a => .int a.toInt64.toInt
  | _ => .none

/-- Python `sorted(iter)` — returns a new sorted list. Uses Lean's
    `List.mergeSort` with a `pyLt`-derived comparator. -/
def pySorted (a : PyVal) : PyVal :=
  let cmp : PyVal → PyVal → Bool := fun x y =>
    match pyLt x y with | .bool b => b | _ => false
  .list ((pyElems a).mergeSort cmp)

/-- Python `range(n)` — produces `[0, 1, …, n-1]`. -/
def pyRange1 : PyVal → PyVal
  | .int n => .list ((List.range n.toNat).map fun i => .int (Int.ofNat i))
  | _ => .list []

/-- Python `range(start, stop)` — produces `[start, start+1, …, stop-1]`. -/
def pyRange2 : PyVal → PyVal → PyVal
  | .int a, .int b =>
    if b ≤ a then .list []
    else .list ((List.range (b - a).toNat).map fun i => .int (a + Int.ofNat i))
  | _, _ => .list []

/-- Python `range(start, stop, step)` — fuel-bounded at 100k iters. -/
def pyRange3 : PyVal → PyVal → PyVal → PyVal
  | .int a, .int b, .int s =>
    if s == 0 then .list []
    else
      -- Build the list by counting required steps. Bounded at 100000
      -- iterations to keep this total — Python's `range(0, 10**18)` would
      -- otherwise blow the heap.
      let count : Nat :=
        if s > 0 then
          if b ≤ a then 0 else ((b - a + s - 1) / s).toNat
        else
          if a ≤ b then 0 else ((a - b + (-s) - 1) / (-s)).toNat
      let bounded := min count 100000
      .list ((List.range bounded).map fun i => .int (a + Int.ofNat i * s))
  | _, _, _ => .list []

/-- Python `enumerate(iter)` — produces `[(0, x0), (1, x1), …]`. -/
def pyEnumerate (a : PyVal) : PyVal :=
  .list ((pyElems a).mapIdx fun i x => .tuple [.int (Int.ofNat i), x])

/-- Python `zip(a, b)` — pairwise tuples; truncates to the shorter. -/
def pyZip (a b : PyVal) : PyVal :=
  let xs := pyElems a
  let ys := pyElems b
  .list ((xs.zip ys).map fun (x, y) => .tuple [x, y])

/-- Python `print(*args)`. We don't model `IO`; the call returns
    `None` and the arguments are evaluated for side-effects upstream. -/
def pyPrint (_ : PyVal) : PyVal := .none

/-- Python `isinstance(x, T)`. We don't carry runtime types other than the
    constructor tags, so this matches via `pyType` against a string-named
    type literal. The user is expected to compare `isinstance(x, "int")`-
    style in tests; the standard `isinstance(x, int)` form passes the
    `int` *type object*, which we don't have, so this falls back to
    `True`. The fallback is conservative: `assert isinstance(x, int)` will
    pass for any `x`, which is the same vacuity as before. -/
def pyIsinstance : PyVal → PyVal → PyVal
  | x, .str tag => match pyType x with | .str t => .bool (t == tag) | _ => .bool false
  | _, _ => .bool true

/-- Python `next(iterator)`. We don't model iterator state; falls back
    to the first element of the iterable, or `.none` if empty. -/
def pyNext : PyVal → PyVal
  | a => match pyElems a with | x :: _ => x | [] => .none

/-- Python `any(iter)`. -/
def pyAny (a : PyVal) : PyVal :=
  .bool ((pyElems a).any pyTruthy)

/-- Python `all(iter)`. -/
def pyAll (a : PyVal) : PyVal :=
  .bool ((pyElems a).all pyTruthy)

/-- Python `list(iter)`. -/
def pyToList (a : PyVal) : PyVal := .list (pyElems a)

/-- Python `tuple(iter)`. -/
def pyToTuple (a : PyVal) : PyVal := .tuple (pyElems a)

/-- Python `reversed(iter)` — produces an iterator over the elements in
    reverse order. We model it as a list. -/
def pyReversed (a : PyVal) : PyVal :=
  .list (pyElems a).reverse

/-- Python `map(fn, iter)` for `fn : PyVal → PyVal`. The codegen
    recognises a small set of builtin functions (`abs`, `str`, `int`,
    `float`, `bool`, `len`, ...) and dispatches `map(builtin, xs)` to
    `pyMap py<Builtin> xs`. Producing a `PyVal.list` (Python `map` is
    actually a lazy iterator, but our model normalises to a list). -/
def pyMap (fn : PyVal → PyVal) (a : PyVal) : PyVal :=
  .list ((pyElems a).map fn)

/-- Python `filter(fn, iter)` for `fn : PyVal → PyVal`. Returns the
    elements where `fn x` is truthy. -/
def pyFilter (fn : PyVal → PyVal) (a : PyVal) : PyVal :=
  .list ((pyElems a).filter (fun x => pyTruthy (fn x)))

-- ----------------------------------------------------------------------------
-- String / list / dict methods (for `obj.method(args)` dispatch)
-- ----------------------------------------------------------------------------
--
-- These mirror the most common Python methods. Codegen detects
-- attribute-call shape `obj.method(args)` and dispatches by method name
-- to one of these helpers (see `Codegen.lean`'s `methodCall` table).
-- Each helper is total and computable.

/-- `s.upper()` — converts ASCII lowercase to uppercase. Non-ASCII passes
    through unchanged. -/
def pyStrUpper : PyVal → PyVal
  | .str s => .str s.toUpper
  | a => a

/-- `s.lower()`. -/
def pyStrLower : PyVal → PyVal
  | .str s => .str s.toLower
  | a => a

/-- `s.strip()` — trim ASCII whitespace from both ends. -/
def pyStrStrip : PyVal → PyVal
  | .str s => .str s.trim
  | a => a

/-- `s.startswith(prefix)`. -/
def pyStrStartsWith : PyVal → PyVal → PyVal
  | .str s, .str p => .bool (s.startsWith p)
  | _, _ => .bool false

/-- `s.endswith(suffix)`. -/
def pyStrEndsWith : PyVal → PyVal → PyVal
  | .str s, .str p => .bool (s.endsWith p)
  | _, _ => .bool false

/-- `s.split(sep)` — split on a separator string. -/
def pyStrSplit : PyVal → PyVal → PyVal
  | .str s, .str sep =>
    if sep.isEmpty then .list [.str s]
    else .list ((s.splitOn sep).map .str)
  | a, _ => a

/-- `s.replace(old, new)`. -/
def pyStrReplace : PyVal → PyVal → PyVal → PyVal
  | .str s, .str a, .str b => .str (s.replace a b)
  | a, _, _ => a

/-- `sep.join(iter)`. -/
def pyStrJoinMethod : PyVal → PyVal → PyVal
  | .str sep, xs =>
    let parts := (pyElems xs).map fun x => match x with | .str s => s | a => pyToStr a
    .str (String.intercalate sep parts)
  | a, _ => a

/-- `s.find(sub)` — first index of `sub` in `s`, or `-1`. -/
def pyStrFind : PyVal → PyVal → PyVal
  | .str s, .str sub =>
    if sub.isEmpty then .int 0
    else
      let parts := s.splitOn sub
      match parts with
      | [] => .int (-1)
      | [_] => .int (-1)
      | first :: _ => .int (Int.ofNat first.length)
  | _, _ => .int (-1)

/-- `s.count(sub)`. -/
def pyStrCount : PyVal → PyVal → PyVal
  | .str s, .str sub =>
    if sub.isEmpty then .int (Int.ofNat s.length + 1)
    else .int (Int.ofNat ((s.splitOn sub).length - 1))
  | _, _ => .int 0

/-- `d.keys()`. -/
def pyDictKeys : PyVal → PyVal
  | .dict d => .list (d.map (·.1))
  | _ => .list []

/-- `d.values()`. -/
def pyDictValues : PyVal → PyVal
  | .dict d => .list (d.map (·.2))
  | _ => .list []

/-- `d.items()`. -/
def pyDictItems : PyVal → PyVal
  | .dict d => .list (d.map fun (k, v) => .tuple [k, v])
  | _ => .list []

/-- `d.get(key, default := .none)`. -/
def pyDictGet : PyVal → PyVal → PyVal := fun d k => pyIndex d k

/-- `d.get(key, default)` — explicit default. -/
def pyDictGetDefault : PyVal → PyVal → PyVal → PyVal
  | .dict d, k, dflt =>
    match pyIndex (.dict d) k with
    | .none => dflt
    | v => v
  | _, _, dflt => dflt

/-- `lst.append(x)` — return a new list with `x` appended. The
    codegen lowers `lst.append(x)` (a Python statement that mutates
    `lst`) to a re-binding `let lst := pyListAppend lst x` so the
    immediately-following `lst` references see the updated value.
    Closes a slice of P1 (mutation precision) for the
    assignment-then-method pattern. -/
def pyListAppend (lst x : PyVal) : PyVal :=
  .list (pyElems lst ++ [x])

/-- `lst.extend(other)` — return a new list with `other`'s elements
    appended. -/
def pyListExtend (lst other : PyVal) : PyVal :=
  .list (pyElems lst ++ pyElems other)

/-- `lst[i] = val` — return a new list with the element at index `i`
    replaced by `val`. Out-of-range indices leave the list unchanged
    (mirrors Python's silent no-op for invalid list assignment via
    the model — real Python raises an IndexError, but the model is
    value-level, not exception-level, for subscript operations). -/
def pyListSet (lst idx val : PyVal) : PyVal :=
  match lst, idx with
  | .list xs, .int i =>
    let n := Int.toNat i
    if n < xs.length then .list (xs.set n val) else .list xs
  | _, _ => lst

/-- `d[k] = v` — return a new dict with key `k` set to `v`. If `k`
    already exists, it is replaced; otherwise it is appended. -/
def pyDictSet (d k v : PyVal) : PyVal :=
  match d with
  | .dict pairs =>
    let filtered := pairs.filter fun (k', _) =>
      match pyEq k k' with | .bool true => false | _ => true
    .dict (filtered ++ [(k, v)])
  | _ => d

/-- `obj[idx] = val` — unified subscript set for both lists and dicts.
    Dispatches on the runtime type of `obj`. -/
def pySubscriptSet (obj idx val : PyVal) : PyVal :=
  match obj with
  | .dict _ => pyDictSet obj idx val
  | .list _ => pyListSet obj idx val
  | _ => obj

/-- `lst.count(x)` — count occurrences. -/
def pyListCount : PyVal → PyVal → PyVal
  | a, x => .int (Int.ofNat ((pyElems a).filter fun y =>
      match pyEq x y with | .bool b => b | _ => false).length)

/-- `lst.index(x)` — first index of `x`, or `-1`. -/
def pyListIndex : PyVal → PyVal → PyVal
  | a, x =>
    let elems := pyElems a
    let rec findAt : List PyVal → Nat → Int
      | [], _ => -1
      | y :: ys, i =>
        match pyEq x y with
        | .bool true => Int.ofNat i
        | _ => findAt ys (i + 1)
    .int (findAt elems 0)

/-- List comprehension `[elem(x) for x in iter if cond(x)]`. The element
    and condition closures both live in `Eff p`, so any effects in either
    flow through to the resulting `Eff p PyVal`. Returns a `PyVal.list`. -/
def pyListComp {p : Perms} (iter : PyVal)
    (elemFn : PyVal → Eff p PyVal) (condFn : PyVal → Eff p PyVal)
    : Eff p PyVal := do
  let mut acc : List PyVal := []
  for x in pyElems iter do
    let keep ← condFn x
    if pyTruthy keep then
      let v ← elemFn x
      acc := acc ++ [v]
  pure (.list acc)

/-- Two-generator list comprehension `[elem(x, y) for x in iter1 for y in iter2(x) if cond(x, y)]`.
    The inner iterable receives the outer-loop variable so each outer
    iteration can produce a different inner iterable (matching Python's
    `[x*y for x in [[1,2], [3]] for y in x]` shape). The condition fires
    after both bindings are in scope. -/
def pyListComp2 {p : Perms} (iter1 : PyVal)
    (iter2Fn : PyVal → Eff p PyVal)
    (elemFn : PyVal → PyVal → Eff p PyVal)
    (condFn : PyVal → PyVal → Eff p PyVal)
    : Eff p PyVal := do
  let mut acc : List PyVal := []
  for x in pyElems iter1 do
    let inner ← iter2Fn x
    for y in pyElems inner do
      let keep ← condFn x y
      if pyTruthy keep then
        let v ← elemFn x y
        acc := acc ++ [v]
  pure (.list acc)

/-- Set comprehension `{elem(x) for x in iter if cond(x)}`. Same shape as
    `pyListComp`; we don't dedupe (sets are modeled as lists in `PyVal`). -/
def pySetComp {p : Perms} (iter : PyVal)
    (elemFn : PyVal → Eff p PyVal) (condFn : PyVal → Eff p PyVal)
    : Eff p PyVal := pyListComp iter elemFn condFn

/-- Three-generator list comprehension. The third iterable receives
    BOTH outer-loop variables, so each `(x, y)` can produce a
    different innermost iterable. Closes precision gap § 2.8. -/
def pyListComp3 {p : Perms} (iter1 : PyVal)
    (iter2Fn : PyVal → Eff p PyVal)
    (iter3Fn : PyVal → PyVal → Eff p PyVal)
    (elemFn : PyVal → PyVal → PyVal → Eff p PyVal)
    (condFn : PyVal → PyVal → PyVal → Eff p PyVal)
    : Eff p PyVal := do
  let mut acc : List PyVal := []
  for x in pyElems iter1 do
    let inner1 ← iter2Fn x
    for y in pyElems inner1 do
      let inner2 ← iter3Fn x y
      for z in pyElems inner2 do
        let keep ← condFn x y z
        if pyTruthy keep then
          let v ← elemFn x y z
          acc := acc ++ [v]
  pure (.list acc)

/-- Two-generator set comprehension. Same as `pyListComp2`; the result
    is a `PyVal.list` (we don't dedupe sets). -/
def pySetComp2 {p : Perms} (iter1 : PyVal)
    (iter2Fn : PyVal → Eff p PyVal)
    (elemFn : PyVal → PyVal → Eff p PyVal)
    (condFn : PyVal → PyVal → Eff p PyVal)
    : Eff p PyVal := pyListComp2 iter1 iter2Fn elemFn condFn

/-- Dict comprehension `{k(x): v(x) for x in iter if cond(x)}`. Returns a
    `PyVal.dict`. -/
def pyDictComp {p : Perms} (iter : PyVal)
    (keyFn : PyVal → Eff p PyVal) (valFn : PyVal → Eff p PyVal)
    (condFn : PyVal → Eff p PyVal)
    : Eff p PyVal := do
  let mut acc : List (PyVal × PyVal) := []
  for x in pyElems iter do
    let keep ← condFn x
    if pyTruthy keep then
      let k ← keyFn x
      let v ← valFn x
      acc := acc ++ [(k, v)]
  pure (.dict acc)

/-- Two-generator dict comprehension `{k(x,y): v(x,y) for x in iter1 for y in iter2(x) if cond(x,y)}`. -/
def pyDictComp2 {p : Perms} (iter1 : PyVal)
    (iter2Fn : PyVal → Eff p PyVal)
    (keyFn : PyVal → PyVal → Eff p PyVal) (valFn : PyVal → PyVal → Eff p PyVal)
    (condFn : PyVal → PyVal → Eff p PyVal)
    : Eff p PyVal := do
  let mut acc : List (PyVal × PyVal) := []
  for x in pyElems iter1 do
    let inner ← iter2Fn x
    for y in pyElems inner do
      let keep ← condFn x y
      if pyTruthy keep then
        let k ← keyFn x y
        let v ← valFn x y
        acc := acc ++ [(k, v)]
  pure (.dict acc)

/-- A bounded `while` driver: runs `body` repeatedly while `cond` is
    truthy, up to `fuel` iterations. The fuel bound ensures termination
    so this is fully computable. Codegen will pick a generous default
    fuel; users wanting a tighter bound can replace the call site.

    Like `pyForEach`, the body's effect set propagates into the result —
    a `Pure` function with a `while` whose body calls a `Net` external
    becomes `Eff { net := true } Unit` and fails to type-check. -/
def pyWhile {p : Perms} (fuel : Nat) (cond : Eff p PyVal) (body : Eff p Unit)
    : Eff p Unit :=
  match fuel with
  | 0 => ⟨.ok ()⟩
  | n + 1 =>
    match cond with
    | ⟨.ok c⟩ =>
      if pyTruthy c then
        match body with
        | ⟨.ok _⟩             => pyWhile n cond body
        | ⟨.error .broke⟩     => ⟨.ok ()⟩            -- break exits the loop
        | ⟨.error .continued⟩ => pyWhile n cond body -- continue → re-test cond
        | ⟨.error c⟩          => ⟨.error c⟩           -- exception/return propagate
      else
        ⟨.ok ()⟩
    | ⟨.error c⟩ => ⟨.error c⟩

-- ============================================================================
-- First-class functions (closures)
-- ============================================================================
--
-- Two paths exist for function-as-value support:
--
-- 1. **Typed `PyClosure p arity`** — carries the closure's effect set
--    `p` and arity in its type. Codegen uses this for **named local
--    lambdas**: `let cb = lambda: send_email(x)` becomes
--    `let cb := PyClosure.mk1 (fun _ => do let _ ← ext_send_email x; pure ...)`.
--    Lean's type inference figures out `cb`'s perms automatically; calling
--    `cb()` from a `Pure` context produces a real type error. This is the
--    backbone of effect tracking through first-class functions.
--
-- 2. **Untyped `PyVal.callFn` family** — polymorphic-in-perms axioms used
--    when a callable flows through `PyVal` (stored in a list, passed as
--    an untyped arg). Necessarily lossy: once a closure goes into a
--    `PyVal`, its perms are erased and the call must be polymorphic.
--    Closing this hole would need effect-indexed `PyVal`.

/-- A typed first-class function value. The effect set `p` and arity are
    encoded in the type so Lean's type checker enforces them at call sites.

    Concrete definition: `PyClosure p 0` is the type of a `Unit → Eff p PyVal`,
    `PyClosure p 1` is `PyVal → Eff p PyVal`, etc. The `mk*` constructors
    are identity, and `call*` is plain function application. The previous
    `axiom`-based formulation was opaque, which forced any function
    holding a `PyClosure` to be `noncomputable`. The concrete form is
    fully reducible, so a `let cb := PyClosure.mk1 (fun x => …)` followed
    by `cb x` reduces by `rfl`. -/
def PyClosure (p : Perms) (n : Nat) : Type :=
  match n with
  | 0  => Unit → Eff p PyVal
  | 1  => PyVal → Eff p PyVal
  | 2  => PyVal → PyVal → Eff p PyVal
  | 3  => PyVal → PyVal → PyVal → Eff p PyVal
  | 4  => PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 5  => PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 6  => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 7  => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 8  => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 9  => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 10 => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 11 => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 12 => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 13 => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 14 => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 15 => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | 16 => PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal
  | _ => Unit -- arities ≥ 17 are not modeled; placeholder unit type

/-- Inhabitant for `PyClosure p n` so `partial def` recursion through
    closure-typed return values can prove non-emptiness. The `unfold`
    is needed because `PyClosure` is a definition, not an inductive. -/
instance : ∀ {p : Perms} {n : Nat}, Inhabited (PyClosure p n)
  | _, 0  => ⟨fun _ => pure PyVal.none⟩
  | _, 1  => ⟨fun _ => pure PyVal.none⟩
  | _, 2  => ⟨fun _ _ => pure PyVal.none⟩
  | _, 3  => ⟨fun _ _ _ => pure PyVal.none⟩
  | _, 4  => ⟨fun _ _ _ _ => pure PyVal.none⟩
  | _, 5  => ⟨fun _ _ _ _ _ => pure PyVal.none⟩
  | _, 6  => ⟨fun _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 7  => ⟨fun _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 8  => ⟨fun _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 9  => ⟨fun _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 10 => ⟨fun _ _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 11 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 12 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 13 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 14 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 15 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, 16 => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => pure PyVal.none⟩
  | _, _ + 17 => ⟨()⟩

/-- Build a 0-arg typed closure from a Lean function. -/
def PyClosure.mk0 {p : Perms} (f : Unit → Eff p PyVal) : PyClosure p 0 := f

/-- Build a 1-arg typed closure. -/
def PyClosure.mk1 {p : Perms} (f : PyVal → Eff p PyVal) : PyClosure p 1 := f

/-- Build a 2-arg typed closure. -/
def PyClosure.mk2 {p : Perms} (f : PyVal → PyVal → Eff p PyVal) : PyClosure p 2 := f

/-- Build a 3-arg typed closure. -/
def PyClosure.mk3 {p : Perms} (f : PyVal → PyVal → PyVal → Eff p PyVal) : PyClosure p 3 := f

/-- Build a 4-arg typed closure. -/
def PyClosure.mk4 {p : Perms} (f : PyVal → PyVal → PyVal → PyVal → Eff p PyVal) : PyClosure p 4 := f

/-- Build a 5-arg typed closure. -/
def PyClosure.mk5 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal) : PyClosure p 5 := f

/-- Build a 6-arg typed closure. -/
def PyClosure.mk6 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 6 := f

/-- Build a 7-arg typed closure. -/
def PyClosure.mk7 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 7 := f

/-- Build an 8-arg typed closure. -/
def PyClosure.mk8 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 8 := f

/-- Build a 9-arg typed closure. -/
def PyClosure.mk9 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 9 := f

/-- Build a 10-arg typed closure. -/
def PyClosure.mk10 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 10 := f

/-- Build an 11-arg typed closure. -/
def PyClosure.mk11 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 11 := f

/-- Build a 12-arg typed closure. -/
def PyClosure.mk12 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 12 := f

/-- Build a 13-arg typed closure. -/
def PyClosure.mk13 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 13 := f

/-- Build a 14-arg typed closure. -/
def PyClosure.mk14 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 14 := f

/-- Build a 15-arg typed closure. -/
def PyClosure.mk15 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 15 := f

/-- Build a 16-arg typed closure. -/
def PyClosure.mk16 {p : Perms}
    (f : PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → PyVal → Eff p PyVal)
    : PyClosure p 16 := f

/-- Call a 0-arg typed closure. Returns `Eff p PyVal`, so the surrounding
    `do` block must accept the closure's effect set — that's how the type
    system enforces effect tracking through closures. The call is wrapped
    in `Eff.runFunction` so an early `return v` inside the closure body
    (which lowers to `Eff.return v` = `.error (.returned v)`) is converted
    back to `.ok v` at the call boundary, matching real function-call
    semantics. Without the wrap, the closure's `return` would propagate
    out of the *caller* — definitely wrong. -/
def PyClosure.call0 {p : Perms} (c : PyClosure p 0) : Eff p PyVal :=
  Eff.runFunction (c ())

/-- Call a 1-arg typed closure. -/
def PyClosure.call1 {p : Perms} (c : PyClosure p 1) (x : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x)

/-- Call a 2-arg typed closure. -/
def PyClosure.call2 {p : Perms} (c : PyClosure p 2) (x y : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x y)

/-- Call a 3-arg typed closure. -/
def PyClosure.call3 {p : Perms} (c : PyClosure p 3) (x y z : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x y z)

/-- Call a 4-arg typed closure. -/
def PyClosure.call4 {p : Perms} (c : PyClosure p 4) (x y z w : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x y z w)

/-- Call a 5-arg typed closure. -/
def PyClosure.call5 {p : Perms} (c : PyClosure p 5)
    (x y z w v : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x y z w v)

/-- Call a 6-arg typed closure. -/
def PyClosure.call6 {p : Perms} (c : PyClosure p 6)
    (x y z w v u : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x y z w v u)

/-- Call a 7-arg typed closure. -/
def PyClosure.call7 {p : Perms} (c : PyClosure p 7)
    (x y z w v u t : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x y z w v u t)

/-- Call an 8-arg typed closure. -/
def PyClosure.call8 {p : Perms} (c : PyClosure p 8)
    (x y z w v u t s : PyVal) : Eff p PyVal :=
  Eff.runFunction (c x y z w v u t s)

/-- Call a 9-arg typed closure. -/
def PyClosure.call9 {p : Perms} (c : PyClosure p 9)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9)

/-- Call a 10-arg typed closure. -/
def PyClosure.call10 {p : Perms} (c : PyClosure p 10)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)

/-- Call an 11-arg typed closure. -/
def PyClosure.call11 {p : Perms} (c : PyClosure p 11)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)

/-- Call a 12-arg typed closure. -/
def PyClosure.call12 {p : Perms} (c : PyClosure p 12)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)

/-- Call a 13-arg typed closure. -/
def PyClosure.call13 {p : Perms} (c : PyClosure p 13)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)

/-- Call a 14-arg typed closure. -/
def PyClosure.call14 {p : Perms} (c : PyClosure p 14)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14)

/-- Call a 15-arg typed closure. -/
def PyClosure.call15 {p : Perms} (c : PyClosure p 15)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)

/-- Call a 16-arg typed closure. -/
def PyClosure.call16 {p : Perms} (c : PyClosure p 16)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : PyVal) : Eff p PyVal :=
  Eff.runFunction (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)

-- ----------------------------------------------------------------------------
-- Untyped closure axioms (closures flowing through PyVal)
-- ----------------------------------------------------------------------------

/-- Wrap a single-arg function as a PyVal — effect-erasing. -/
axiom PyVal.ofFn {p : Perms} : (PyVal → Eff p PyVal) → PyVal

/-- Wrap a zero-arg function as a PyVal. -/
axiom PyVal.ofFn0 {p : Perms} : (Unit → Eff p PyVal) → PyVal

/-- Wrap a multi-arg (2) function as a PyVal. -/
axiom PyVal.ofFn2 {p : Perms} : (PyVal → PyVal → Eff p PyVal) → PyVal

/-- Wrap a pure single-arg function as a PyVal. -/
def PyVal.ofPureFn (_f : PyVal → PyVal) : PyVal := .none

/-- Call a PyVal that holds a zero-arg function. **Fixed at `Perms.top`** —
    once a callable is erased into an untyped `PyVal`, we have no idea
    which effects its body uses, so we conservatively assume *all* of them.
    Any function calling `PyVal.callFn0` must itself be declared at
    `Perms.top` (or a wider set). The previous `{p : Perms}`-polymorphic
    typing was unsound: it let callers instantiate `p := Perms.none` in
    a `Pure` context, hiding arbitrary effects. -/
axiom PyVal.callFn0 : PyVal → Eff Perms.top PyVal

/-- Call a PyVal that holds a single-arg function. Fixed at `Perms.top`
    — see `PyVal.callFn0` for the rationale. -/
axiom PyVal.callFn : PyVal → PyVal → Eff Perms.top PyVal

/-- Call a PyVal that holds a two-arg function. Fixed at `Perms.top`
    — see `PyVal.callFn0` for the rationale. -/
axiom PyVal.callFn2 : PyVal → PyVal → PyVal → Eff Perms.top PyVal

-- ============================================================================
-- EffAST: introspectable representation for symbolic execution
-- ============================================================================
--
-- The codegen emits each function's body twice:
-- (1) as a string-based `Eff` term (the `def <name>`) for type-checking,
--     evaluation, and assertion proofs;
-- (2) as an `EffAST` value (the `def <name>__ast`) for symbolic-execution
--     analyses like "is `a` called before every call to `b`?".
--
-- The two are derived from the same IR by the same codegen, so they're
-- guaranteed to agree by construction. The AST is a *defunctionalized
-- free monad* — the `bind` constructor uses a HOAS continuation
-- (`PyVal → EffAST`) to bind sub-results, while branches and exception
-- handlers are exposed as structural constructors so analyses can walk
-- both arms.
--
-- The HOAS bind continuation is a Lean function — we can't
-- pattern-match on it, only call it. For ordering analysis we don't
-- need the actual call result, so we walk the continuation by passing
-- `PyVal.none` as a placeholder. Branch coverage is still complete
-- because `branchOn` exposes both arms as separate sub-ASTs (the
-- codegen lowers Python `if/else` to `branchOn`, not to a Lean
-- `if/then/else` inside a continuation).

inductive EffAST where
  /-- Final pure value. No more effects. -/
  | pure    : PyVal → EffAST
  /-- Sequence: run `e`, discard its result, run `k`. Path B
      refactor replaced an earlier HOAS form (`EffAST → (PyVal →
      EffAST) → EffAST`) with this first-order variant. The codegen
      always emitted the HOAS continuation as `fun _ => ...`, so no
      information is lost — and every analysis (`permsOf`,
      `mustCalled`, etc.) is now purely structural on the AST. -/
  | seq     : EffAST → EffAST → EffAST
  /-- Call a top-level name (external or local function). The string is
      the codegen-sanitized name; the args are the call arguments
      (currently treated as opaque PyVals — the analyses care about the
      callee, not the args). -/
  | call    : String → List PyVal → EffAST
  /-- `if cond then a else b`. Both arms are exposed structurally so
      analyses can walk both. The condition value isn't used by
      ordering analyses (they consider all paths). -/
  | branchOn : PyVal → EffAST → EffAST → EffAST
  /-- `try body except handler`. Both arms are exposed structurally. -/
  | tryExc  : EffAST → EffAST → EffAST
  /-- A bounded loop body that may run 0+ times. Ordering analyses
      treat this as "may have run, may have not" — calls inside the
      loop body are NOT added to the must-set after the loop. -/
  | loop    : EffAST → EffAST
  /-- Raise an exception. Terminates the current AST branch. -/
  | raise   : PyVal → EffAST
  /-- Early `return`. Terminates the current AST branch. -/
  | retEarly : PyVal → EffAST
  /-- Fallback for IR shapes the AST translator doesn't yet handle.
      Analyses that hit this return a "don't know" verdict (they
      conservatively reject the property under analysis). -/
  | opaque  : EffAST

namespace EffAST

/-- Interpret an `EffAST` back into the executable `Eff` monad. This is
    here mostly for the symmetry — `def <name>` and `def <name>__ast`
    are both emitted by the codegen, so we don't actually need to
    interpret in production. The interpreter is `Perms.top`-typed
    because we lose perms information at the AST level. -/
partial def interp : EffAST → Eff Perms.top PyVal
  | .pure v => Pure.pure v
  | .seq e k => do let _ ← interp e; interp k
  | .call _ _ => Pure.pure PyVal.none
  | .branchOn cond a b => if pyTruthy cond then interp a else interp b
  | .tryExc t h => Eff.tryCatch (interp t) (fun _ => interp h)
  | .loop _ => Pure.pure PyVal.none  -- model loops as no-ops at the value level
  | .raise v => Eff.raise v
  | .retEarly v => Eff.return v
  | .opaque => Pure.pure PyVal.none

-- ============================================================================
-- Symbolic-execution analyses
-- ============================================================================

/-- The set of names that must have been called along EVERY path through
    `e`, computed with a fuel bound to keep the recursion total. -/
def mustCalled : Nat → EffAST → List String
  | 0,     _ => []  -- ran out of fuel; conservative under-approximation
  | _+1,   .pure _ => []
  | _+1,   .raise _ => []
  | _+1,   .retEarly _ => []
  | _+1,   .opaque => []
  | _+1,   .call name _ => [name]
  | f+1,   .seq e k =>
    let xs := mustCalled f e
    let ys := mustCalled f k
    xs ++ ys.filter (fun n => !xs.contains n)
  | f+1,   .branchOn _ a b =>
    -- Intersection: a name is must-called only if both arms call it.
    let xs := mustCalled f a
    let ys := mustCalled f b
    xs.filter (fun n => ys.contains n)
  | f+1,   .tryExc t h =>
    -- The handler might fire instead of the try body. So a name is
    -- must-called only if BOTH arms call it.
    let xs := mustCalled f t
    let ys := mustCalled f h
    xs.filter (fun n => ys.contains n)
  | _+1,   .loop _ =>
    -- Loop body may run 0 times. Conservatively: nothing in the body
    -- is must-called.
    []

/-- True iff every call to `b` in `e` is preceded (on every path) by a
    call to `a`. The fuel parameter bounds the recursion depth into
    HOAS continuations.

    Algorithm: walk `e`, threading the set of names that have been
    called so far on the current path. At each `call b _` site, check
    that `a` is in the set. -/
def calledBeforeAux (a b : String) : Nat → List String → EffAST → Bool
  | 0,     _,      _ => false
  | _+1,   _,      .pure _ => true
  | _+1,   _,      .raise _ => true
  | _+1,   _,      .retEarly _ => true
  | _+1,   _,      .opaque => false  -- can't prove anything past an opaque region
  | _+1,   called, .call name _ =>
    if name == b then called.contains a
    else true
  | f+1,   called, .seq e k =>
    if !calledBeforeAux a b f called e then false
    else
      -- After `e`, the names called by `e` are added to the set.
      let calledAfter := called ++ mustCalled f e
      calledBeforeAux a b f calledAfter k
  | f+1,   called, .branchOn _ ifT ifF =>
    calledBeforeAux a b f called ifT && calledBeforeAux a b f called ifF
  | f+1,   called, .tryExc t h =>
    calledBeforeAux a b f called t && calledBeforeAux a b f called h
  | f+1,   called, .loop body =>
    -- Loop body may run any number of times. The post-state of the
    -- loop is unchanged (body may run 0 times), but the body itself
    -- still needs to be analyzed. However, we don't add the body's
    -- calls to the must-set — they may not have happened.
    calledBeforeAux a b f called body

/-- Top-level entry point with a default fuel of 1024 — large enough
    for any practical function body, small enough that `native_decide`
    discharges in milliseconds. -/
def calledBefore (a b : String) (e : EffAST) : Bool :=
  calledBeforeAux a b 1024 [] e

-- ============================================================================
-- permsOf: the call-graph fixpoint as a pure function over EffAST
-- ============================================================================
--
-- `permsOf` computes the effect set of an `EffAST` by unioning the
-- perms of every call it contains, recursing into local-function
-- callees via a `FuncEnv` (the reverse-direction map from local
-- function names to their ASTs). External perms come from an
-- `ExtEnv` (name → declared Perms). Names that aren't in either
-- environment widen to `Perms.top` — this matches the codegen's
-- treatment of unknown externals (G1) and dynamic dispatch.
--
-- This mirrors the fixpoint currently running in `Codegen.lean`
-- (`inferredPermsMap`), but expressed as a structural recursion on
-- the AST. The `Phase A` design doc (`docs/phase-a-design.md`)
-- explains how this becomes the single source of truth for
-- per-function perms, replacing the codegen-side fixpoint entirely.
--
-- The `visited` list breaks recursion: when walking a local callee,
-- we refuse to re-enter a name we've already expanded in the
-- current walk. This makes `permsOf` total even on mutually
-- recursive call graphs — the fuel bound is a belt-and-braces
-- safeguard for pathological depths.

/-- Reverse-direction map from local function names (the sanitised
    Lean names, e.g. `"fetch_one"`) to their `EffAST` bodies. Built
    by the codegen at module scope. Same shape as the `locals`
    parameter used by `calledBeforeInter`. -/
abbrev FuncEnv := List (String × EffAST)

/-- Environment of external functions → their declared perms. Names
    use the `ext_`-prefixed sanitised form the codegen emits (e.g.
    `"ext_send_email"`). Lookups that miss this environment fall
    through to the local `FuncEnv`; lookups that miss both widen to
    `Perms.top`. -/
abbrev ExtEnv := List (String × Perms)

/-- Structural recursion over `EffAST` producing the union of all
    perms reachable from `e`. The `visited` list is the set of
    local-function names currently being expanded — entering one a
    second time short-circuits to `Perms.none` (its calls will be
    accounted for in the outer expansion).

    Total (a plain `def`, not `partial`), so the kernel unfolds it
    during type checking — which is what makes
    `def foo : Eff (permsOf ...) PyVal := body` reduce to a ground
    perms literal at elaboration time under Phase A. The structural
    decrease is on the `Nat` fuel parameter. Same fuel convention
    as `mustCalled`, `calledBefore`, etc. -/
def permsOfAux (extEnv : ExtEnv) (env : FuncEnv)
    : Nat → List String → EffAST → Perms
  | 0,     _,       _ => Perms.top  -- fuel exhausted → conservative
  | _+1,   _,       .pure _ => Perms.none
  | _+1,   _,       .opaque => Perms.top
  | _+1,   _,       .raise _ => Perms.none
  | _+1,   _,       .retEarly _ => Perms.none
  | f+1,   visited, .call name _ =>
    -- Externals take priority; then locals; then unknown → top.
    match extEnv.find? (·.1 == name) with
    | some (_, p) => p
    | none =>
      match env.find? (·.1 == name) with
      | some (_, body) =>
        if visited.contains name then Perms.none
        else permsOfAux extEnv env f (name :: visited) body
      | none => Perms.top
  | f+1,   visited, .seq e k =>
    let p1 := permsOfAux extEnv env f visited e
    let p2 := permsOfAux extEnv env f visited k
    Perms.union p1 p2
  | f+1,   visited, .branchOn _ a b =>
    Perms.union (permsOfAux extEnv env f visited a)
                (permsOfAux extEnv env f visited b)
  | f+1,   visited, .tryExc t h =>
    Perms.union (permsOfAux extEnv env f visited t)
                (permsOfAux extEnv env f visited h)
  | f+1,   visited, .loop body =>
    permsOfAux extEnv env f visited body

/-- Top-level entry point. Defaults to fuel 1024, same convention as
    `calledBefore` / `calledBeforeInter`. -/
def permsOf (extEnv : ExtEnv) (env : FuncEnv) (e : EffAST) : Perms :=
  permsOfAux extEnv env 1024 [] e

end EffAST

namespace EffAST

-- ============================================================================
-- Interprocedural symbolic execution
-- ============================================================================
--
-- The intra-procedural `calledBefore` only walks one function's AST.
-- Real agent code is usually split across helper functions, so the
-- interprocedural form takes a *call table* mapping local function
-- names to their `EffAST` values, and inlines those bodies at call
-- sites. Recursion is handled by a visited-set.

/-- Interprocedural variant of `mustCalled`. When the walker hits a
    `.call name` whose `name` is in the `locals` table, it recurses
    into the callee's AST so calls inside the callee count toward the
    must-set. The visited-set guards against infinite recursion. -/
def mustCalledInter : Nat → List String → List (String × EffAST) → EffAST → List String
  | 0,     _,       _,      _ => []
  | _+1,   _,       _,      .pure _ => []
  | _+1,   _,       _,      .raise _ => []
  | _+1,   _,       _,      .retEarly _ => []
  | _+1,   _,       _,      .opaque => []
  | f+1,   visited, locals, .call name _ =>
    let direct := [name]
    let inlined :=
      if visited.contains name then []
      else match locals.find? (·.1 == name) with
        | some (_, callee) =>
          mustCalledInter f (name :: visited) locals callee
        | none => []
    direct ++ inlined.filter (fun n => !direct.contains n)
  | f+1,   visited, locals, .seq e k =>
    let xs := mustCalledInter f visited locals e
    let ys := mustCalledInter f visited locals k
    xs ++ ys.filter (fun n => !xs.contains n)
  | f+1,   visited, locals, .branchOn _ a b =>
    let xs := mustCalledInter f visited locals a
    let ys := mustCalledInter f visited locals b
    xs.filter (fun n => ys.contains n)
  | f+1,   visited, locals, .tryExc t h =>
    let xs := mustCalledInter f visited locals t
    let ys := mustCalledInter f visited locals h
    xs.filter (fun n => ys.contains n)
  | _+1,   _,       _,      .loop _ => []

/-- Interprocedural variant of `calledBeforeAux`. Inlines local
    function calls at the call site so cross-function ordering works.

    Algorithm: walk `e`, threading the called set. At each `.call b`
    site, check `called.contains a`. At each `.call name` where
    `name` is a local (and not currently visited), recurse into the
    callee's AST so the property is checked through the callee too.
    The `bind` step extends `called` with the callee's must-set.

    ## Soundness of the visited-set on recursive calls

    When the walker encounters a `.call name` where `name` is in
    `visited`, it returns `true` (the optimistic answer). This is
    sound based on the following argument:

    Let `outer` be the first entry to the function `name` on the
    current analysis stack (i.e. the frame that pushed `name` onto
    `visited`). Let `inner` be the recursive re-entry that just
    triggered the visited check. Let `C0 = outer.entryCalled` and
    `C1 = inner.entryCalled`.

    Claim: `C1 ⊇ C0`. The recursive entry happened AFTER the outer's
    body executed some statements that augmented `called`. The
    augmentations only ADD names (the `bind` step uses `called ++
    mustCalled e`). So `C1 ⊇ C0`.

    At any b-check site inside `name`'s body, both outer and inner
    would compute `called = entryCalled + intra-prefix` (the same
    `intra-prefix` for both, since they're walking the same body).
    So `inner.called-at-b-check ⊇ outer.called-at-b-check`.

    If outer passes (i.e. `a ∈ outer.called-at-b-check`), then
    `a ∈ inner.called-at-b-check` too (superset). So inner passes
    whenever outer passes — and the OUTER analysis is the one
    currently in progress that will catch any actual failure.
    Skipping the inner re-entry is sound.

    Tested via `examples/stress_mutual_recursion.py` and three
    additional sanity checks in the EffAST.calledBeforeInter test
    suite. -/
def calledBeforeInterAux (a b : String) (locals : List (String × EffAST))
    : Nat → List String → List String → EffAST → Bool
  | 0,     _,       _,      _ => false
  | _+1,   _,       _,      .pure _ => true
  | _+1,   _,       _,      .raise _ => true
  | _+1,   _,       _,      .retEarly _ => true
  | _+1,   _,       _,      .opaque => false
  | f+1,   visited, called, .call name _ =>
    if name == b then called.contains a
    else
      if visited.contains name then true
      else match locals.find? (·.1 == name) with
        | some (_, callee) =>
          calledBeforeInterAux a b locals f (name :: visited) called callee
        | none => true
  | f+1,   visited, called, .seq e k =>
    if !calledBeforeInterAux a b locals f visited called e then false
    else
      let calledAfter := called ++ mustCalledInter f visited locals e
      calledBeforeInterAux a b locals f visited calledAfter k
  | f+1,   visited, called, .branchOn _ ifT ifF =>
    calledBeforeInterAux a b locals f visited called ifT
    && calledBeforeInterAux a b locals f visited called ifF
  | f+1,   visited, called, .tryExc t h =>
    calledBeforeInterAux a b locals f visited called t
    && calledBeforeInterAux a b locals f visited called h
  | f+1,   visited, called, .loop body =>
    calledBeforeInterAux a b locals f visited called body

/-- Top-level interprocedural entry point. `locals` is a table of
    local function name → AST mappings; the walker inlines them at
    call sites. Default fuel of 1024. -/
def calledBeforeInter (a b : String) (locals : List (String × EffAST))
    (e : EffAST) : Bool :=
  calledBeforeInterAux a b locals 1024 [] [] e

end EffAST

namespace EffAST

-- ============================================================================
-- More symbolic-execution properties
-- ============================================================================

/-- Count how many times `target` appears as a `.call` along an
    `EffAST` path. Branches return the MAX count across arms (an
    upper bound). Loops contribute the body count multiplied by an
    unknown (we conservatively return 0 for loops, so the property
    holds vacuously inside loops). -/
def callCount (target : String) : Nat → EffAST → Nat
  | 0,     _ => 0
  | _+1,   .pure _ => 0
  | _+1,   .raise _ => 0
  | _+1,   .retEarly _ => 0
  | _+1,   .opaque => 0
  | _+1,   .call name _ => if name == target then 1 else 0
  | f+1,   .seq e k => callCount target f e + callCount target f k
  | f+1,   .branchOn _ a b =>
    let xa := callCount target f a
    let xb := callCount target f b
    if xa < xb then xb else xa
  | f+1,   .tryExc t h =>
    let xt := callCount target f t
    let xh := callCount target f h
    if xt < xh then xh else xt
  | _+1,   .loop _ => 0

/-- Returns `true` iff `target` is called exactly once on every path.
    Implementation: walk the AST in two passes — one MIN count and
    one MAX count over branches. For exact-once, both must equal 1
    on every reachable path. We approximate: a single forward pass
    that returns true iff every reachable arm contains exactly one
    call to `target`. -/
def calledExactlyOnceAux (target : String) : Nat → Nat → EffAST → Option Nat
  -- Returns the count along this path; `none` means the analysis
  -- couldn't decide (opaque region, loop body containing target).
  | 0,     _,     _ => none
  | _+1,   acc,   .pure _ => some acc
  | _+1,   acc,   .raise _ => some acc
  | _+1,   acc,   .retEarly _ => some acc
  | _+1,   _,     .opaque => none
  | _+1,   acc,   .call name _ =>
    some (if name == target then acc + 1 else acc)
  | f+1,   acc,   .seq e k =>
    match calledExactlyOnceAux target f acc e with
    | none => none
    | some acc' => calledExactlyOnceAux target f acc' k
  | f+1,   acc,   .branchOn _ a b =>
    match calledExactlyOnceAux target f acc a, calledExactlyOnceAux target f acc b with
    | some xa, some xb => if xa == xb then some xa else none
    | _, _ => none
  | f+1,   acc,   .tryExc t h =>
    match calledExactlyOnceAux target f acc t, calledExactlyOnceAux target f acc h with
    | some xt, some xh => if xt == xh then some xt else none
    | _, _ => none
  | f+1,   acc,   .loop body =>
    -- Loop body may run 0+ times. If body contains `target`, the
    -- count is unbounded. Conservatively: if body contains target,
    -- return none; else propagate acc.
    if callCount target f body > 0 then none
    else some acc

/-- True iff `target` is called exactly once on every reachable
    return path through `e`. Returns false on opaque regions and on
    branches that don't agree on the count. -/
def calledExactlyOnce (target : String) (e : EffAST) : Bool :=
  match calledExactlyOnceAux target 1024 0 e with
  | some 1 => true
  | _ => false

/-- True iff no path through `e` calls both `a` and `b`. -/
def mutuallyExclusiveAux (a b : String)
    : Nat → Bool → Bool → EffAST → Bool
  -- The two Bool flags track whether `a` and `b` have been seen on
  -- the current path. If both are true, return false. We propagate
  -- conjunctively through binds (the next arm starts with the
  -- accumulated flags) and disjunctively through branches (each
  -- branch is a separate path).
  | 0,     _,    _,    _ => false
  | _+1,   _,    _,    .pure _ => true
  | _+1,   _,    _,    .raise _ => true
  | _+1,   _,    _,    .retEarly _ => true
  | _+1,   _,    _,    .opaque => false
  | _+1,   sawA, sawB, .call name _ =>
    let sawA' := sawA || name == a
    let sawB' := sawB || name == b
    !(sawA' && sawB')
  | f+1,   sawA, sawB, .seq e k =>
    -- Walk e first; we need to know its "saw" state to thread into k.
    -- Approximation: walk e checking for violation, then walk k with
    -- the OR of e's contributions. For exact tracking we'd need a
    -- richer return type. Use callCount as a coarse approximation.
    if !mutuallyExclusiveAux a b f sawA sawB e then false
    else
      let sawA' := sawA || (callCount a f e > 0)
      let sawB' := sawB || (callCount b f e > 0)
      mutuallyExclusiveAux a b f sawA' sawB' k
  | f+1,   sawA, sawB, .branchOn _ ifT ifF =>
    mutuallyExclusiveAux a b f sawA sawB ifT
    && mutuallyExclusiveAux a b f sawA sawB ifF
  | f+1,   sawA, sawB, .tryExc t h =>
    mutuallyExclusiveAux a b f sawA sawB t
    && mutuallyExclusiveAux a b f sawA sawB h
  | f+1,   sawA, sawB, .loop body =>
    mutuallyExclusiveAux a b f sawA sawB body

/-- True iff no path through `e` calls both `a` and `b`. -/
def mutuallyExclusive (a b : String) (e : EffAST) : Bool :=
  mutuallyExclusiveAux a b 1024 false false e

/-- True iff every call to `a` in `e` is FOLLOWED (on every path) by
    a call to `b`. The dual of `calledBefore`: where `calledBefore a
    b` walks forward and checks `a` is in the past at each `b`,
    `calledAfter a b` walks forward and checks `b` is in the future
    at each `a`.

    Implementation: at each `.call a` site, check that `b` is in the
    must-set of the REMAINING continuation. -/
def calledAfterAux (a b : String) : Nat → EffAST → Bool
  | 0,     _ => false
  | _+1,   .pure _ => true
  | _+1,   .raise _ => true
  | _+1,   .retEarly _ => true
  | _+1,   .opaque => false
  | _+1,   .call name _ =>
    -- A leaf `.call a` with no continuation means `b` does NOT
    -- follow (the call is the last thing on this path).
    if name == a then false else true
  | f+1,   .seq e k =>
    -- If e's leaf is a call to a, the continuation k must contain b
    -- in its must-set.
    let kMust := mustCalled f k
    let eMust := mustCalled f e
    let eHasUnsafeCallA :=
      -- conservative: if e contains a `.call a` not followed by b
      -- *within* e or k, the property fails.
      callCount a f e > 0 && !(kMust.contains b || eMust.contains b)
    if eHasUnsafeCallA then false
    else calledAfterAux a b f k
  | f+1,   .branchOn _ ifT ifF =>
    calledAfterAux a b f ifT && calledAfterAux a b f ifF
  | f+1,   .tryExc t h =>
    calledAfterAux a b f t && calledAfterAux a b f h
  | f+1,   .loop body =>
    calledAfterAux a b f body

/-- True iff every call to `a` is followed (on every path) by a
    call to `b`. -/
def calledAfter (a b : String) (e : EffAST) : Bool :=
  calledAfterAux a b 1024 e

/-- True iff every reachable return path calls `target` at least
    once. (Opposite of "may not be called" — `eventuallyCalls` is
    "must be called eventually".) Implementation: every path's
    must-set contains `target`. -/
def eventuallyCalls (target : String) (e : EffAST) : Bool :=
  (mustCalled 1024 e).contains target

end EffAST

-- ============================================================================
-- EffProg: full-fidelity program IR for interpretation-based codegen
-- ============================================================================
--
-- `EffAST` (above) is a skeleton that captures only enough of a
-- function's structure to compute `permsOf` and the symbolic-
-- execution properties. Its `interp` is `Perms.top`-typed and
-- fakes loops as no-ops — fine for type checking, but it can't
-- reproduce the executable body's value-level behaviour.
--
-- `EffProg` is the complementary, full-fidelity program
-- representation. It encodes every primitive operation
-- (`pyAdd`, `pyLen`, `pyForEach`, literals, parameter refs,
-- control flow with real continuations) the executable translator
-- currently emits. `EffProg.interp` is a total, dependently-typed
-- function producing `Eff p PyVal` at the same perm as the
-- function's `EffAST` would — the two are tied by the codegen
-- emitting both forms from the same IR.
--
-- Goal: eventually every executable `def foo` in a generated file
-- becomes `def foo := EffProg.interp ... foo__prog`, replacing the
-- hand-built do-block emission. The executable translator is
-- deleted when every shape used by the corpus has an `EffProg`
-- constructor and a matching `interp` arm.
--
-- This universe is introduced INCREMENTALLY. Each pass adds new
-- constructors and migrates one more shape of function. See
-- `docs/effast-full-ir-plan.md` for the pass structure.

namespace EffProg

/-- Binary operators — a small enumeration. `.apply` maps each to
    the corresponding `pyXxx` primitive on `PyVal`. Expanded as
    the corpus forces more cases. -/
inductive BinOp where
  | add | sub | mul | div | mod | floorDiv
  | eq  | ne  | lt  | le  | gt  | ge
  | and_ | or_
  deriving Repr, DecidableEq, Inhabited

/-- Unary operators. Similarly expanded as needed. -/
inductive UnOp where
  | neg | pos | not_ | invert
  deriving Repr, DecidableEq, Inhabited

/-- Expressions: pure value-producing terms. An `Expr` never has
    effects on its own — effects come from `EffProg.call` in the
    surrounding statement context. Expressions appear inside
    `EffProg` statements (as return values, branch conditions,
    call arguments, etc.).

    This is an intentionally small universe for Pass 1. Subsequent
    passes add: `subscript`, `attrGet`, `list`/`dict`/`tuple`,
    `ifElse`, `fstring`, `lambda`, `comprehension` variants. -/
inductive Expr where
  | lit       : PyVal → Expr
  | param     : Nat → Expr                 -- de Bruijn positional param / local
  | binOp     : BinOp → Expr → Expr → Expr
  | unOp      : UnOp → Expr → Expr
  /-- Subscript access: `x[i]`. Interp calls `pyIndex`. -/
  | subscript : Expr → Expr → Expr
  /-- Attribute access: `obj.attr`. Interp returns `PyVal.none`
      (matches G2 value-erased semantics for attributes — the
      attribute's value is only known through declared perms).
      Carrying the attr name for potential future dispatch. -/
  | attrGet   : Expr → String → Expr
  /-- List literal `[e1, e2, ...]`. -/
  | list      : List Expr → Expr
  /-- Tuple literal `(e1, e2, ...)`. -/
  | tuple     : List Expr → Expr
  /-- Dict literal `{k1: v1, k2: v2, ...}`. -/
  | dict      : List (Expr × Expr) → Expr
  /-- Set literal `{e1, e2, ...}`. Interp produces a
      `PyVal.list` (the value model doesn't distinguish sets
      from lists). -/
  | set_      : List Expr → Expr
  /-- Ternary `x if cond else y`. -/
  | ifElse    : Expr → Expr → Expr → Expr
  /-- Module-level global or axiom reference. Looked up in the
      interp's `globals` env by name; if not present, falls
      back to `PyVal.none`. Used for `axiom foo : PyVal`
      references and module-level globals. -/
  | globalRef : String → Expr
  /-- Builtin function applied to one argument: `len(x)`,
      `str(x)`, `abs(x)`, etc. Dispatched to a fixed table in
      `Expr.eval`. Pure by definition (none of these have
      effects). -/
  | builtin1  : String → Expr → Expr
  /-- F-string. Each part is either a literal string fragment
      (`.inl s`) or an interpolation expression (`.inr e`). At
      eval time, parts are concatenated via `pyToStr` on
      interpolated values and joined into a single `PyVal.str`. -/
  | fstring   : List (String ⊕ Expr) → Expr
  /-- Slicing: `x[start:stop:step]`. Each bound is optional. -/
  | slice     : Expr → Option Expr → Option Expr → Option Expr → Expr
  /-- Subscript set: `pySubscriptSet obj idx val`. Pure — returns
      the updated collection. -/
  | subscriptSet : Expr → Expr → Expr → Expr
  /-- List append: `pyListAppend lst val`. Returns new list. -/
  | listAppend : Expr → Expr → Expr
  deriving Repr, Inhabited

/-- `Env` is the positional parameter environment. `param 0` is
    the function's first argument. Local `let`-bindings are
    appended to this list in the `.letIn` case of `EffProg`. -/
abbrev Env := List PyVal

/-- Reduce a `BinOp` to its `pyXxx` primitive. -/
def BinOp.apply : BinOp → PyVal → PyVal → PyVal
  | .add,      a, b => pyAdd a b
  | .sub,      a, b => pySub a b
  | .mul,      a, b => pyMul a b
  | .div,      a, b => pyDiv a b
  | .mod,      a, b => pyMod a b
  | .floorDiv, a, b => pyFloorDiv a b
  | .eq,       a, b => pyEq a b
  | .ne,       a, b => PyVal.bool (!(pyEq a b == PyVal.bool true))
  | .lt,       a, b => pyLt a b
  | .le,       a, b => pyLe a b
  | .gt,       a, b => pyGt a b
  | .ge,       a, b => pyGe a b
  | .and_,     a, b => PyVal.bool (pyTruthy a && pyTruthy b)
  | .or_,      a, b => PyVal.bool (pyTruthy a || pyTruthy b)

def UnOp.apply : UnOp → PyVal → PyVal
  | .neg,    a => pyNeg a
  | .pos,    a => a
  | .not_,   a => PyVal.bool (!(pyTruthy a))
  | .invert, a => pyNeg a  -- approximate for ints

/-- Apply a named builtin to a single argument. Returns
    `PyVal.none` for unknown builtins (value-erasing fallback). -/
def applyBuiltin1 : String → PyVal → PyVal
  | "len",  x | "Len", x => pyLen x
  | "str",  x | "Str", x => pyStr x
  | "bool", x | "Bool", x => PyVal.bool (pyTruthy x)
  | "abs",  x | "Abs", x =>
    match x with
    | .int n  => .int n.natAbs
    | _       => x
  | "int",  x | "Int", x =>
    match x with
    | .int _ => x
    | .float f => .int f.toUInt64.toNat
    | .bool b => .int (if b then 1 else 0)
    | .str s => match s.toInt? with | some n => .int n | none => .none
    | _ => .none
  | _, _ => PyVal.none

-- Evaluate an `Expr` in an env. Total and pure — mutual
-- recursion with `evalList`/`evalDict` for collection
-- constructors, since Lean's structural-recursion checker
-- doesn't see `es.map eval` as decreasing on the ADT.
mutual

def Expr.eval (env : Env) : Expr → PyVal
  | .lit v       => v
  | .param n     => env.getD n PyVal.none
  | .binOp op a b => BinOp.apply op (Expr.eval env a) (Expr.eval env b)
  | .unOp  op a   => UnOp.apply op (Expr.eval env a)
  | .subscript a i => pyIndex (Expr.eval env a) (Expr.eval env i)
  | .attrGet _ _   => PyVal.none
  | .list es     => PyVal.list (Expr.evalList env es)
  | .tuple es    => PyVal.tuple (Expr.evalList env es)
  | .set_ es     => PyVal.list (Expr.evalList env es)
  | .dict kvs    => PyVal.dict (Expr.evalDict env kvs)
  | .ifElse cond t e =>
    if pyTruthy (Expr.eval env cond) then Expr.eval env t else Expr.eval env e
  | .globalRef _ => PyVal.none  -- axioms are value-erased; matches G2
  | .builtin1 name arg => applyBuiltin1 name (Expr.eval env arg)
  | .fstring parts =>
    PyVal.str (Expr.evalFstring env parts)
  | .slice obj start stop step =>
    let startV := match start with | some e => Expr.eval env e | none => PyVal.none
    let stopV  := match stop  with | some e => Expr.eval env e | none => PyVal.none
    let stepV  := match step  with | some e => Expr.eval env e | none => PyVal.none
    pySlice (Expr.eval env obj) startV stopV stepV
  | .subscriptSet obj idx val =>
    pySubscriptSet (Expr.eval env obj) (Expr.eval env idx) (Expr.eval env val)
  | .listAppend lst val =>
    pyListAppend (Expr.eval env lst) (Expr.eval env val)

def Expr.evalFstring (env : Env) : List (String ⊕ Expr) → String
  | [] => ""
  | .inl s :: rest => s ++ Expr.evalFstring env rest
  | .inr e :: rest => pyToStr (Expr.eval env e) ++ Expr.evalFstring env rest

def Expr.evalList (env : Env) : List Expr → List PyVal
  | [] => []
  | e :: es => Expr.eval env e :: Expr.evalList env es

def Expr.evalDict (env : Env) : List (Expr × Expr) → List (PyVal × PyVal)
  | [] => []
  | (k, v) :: kvs => (Expr.eval env k, Expr.eval env v) :: Expr.evalDict env kvs

end

/-- External declaration table for `EffProg.interp` — separate
    from `EffAST.ExtEnv` (same shape, different namespace). -/
abbrev ExtEnv := List (String × Perms)

/-- `EffProg.Prog` — the statement-level program IR. Each
    constructor maps to a specific `Eff` term shape that `interp`
    produces. Named `Prog` (not `EffProg`) so that qualified
    references from generated code (`EffProg.Prog.retWith`, etc.)
    disambiguate from the enclosing namespace.

    Pass 1 universe (pure): `pureStmt`, `seq`, `letIn`, `retWith`,
    `yieldVal`.
    Pass 2 adds: `call`.
    Pass 3: `forEach`, `forFold`.
    Pass 4: `branchOn`, `raiseExc`, `assertStmt`.
    Later passes: `whileBody`, `tryExc`, ... -/
inductive Prog where
  /-- No-op statement. Useful as the tail of a function body. -/
  | pureStmt : Prog
  /-- Sequence two statements. The first's result is discarded. -/
  | seq      : Prog → Prog → Prog
  /-- Bind an expression's value as a new local, then continue. -/
  | letIn    : Expr → Prog → Prog
  /-- Effectful let: run a sub-`Prog`, bind its result value as a
      new local, then continue. Used when the RHS is a `.call` or
      any other effectful statement whose return value is needed
      later. Perms = union of sub's perms and continuation's. -/
  | letInEff : Prog → Prog → Prog
  /-- Early-return with a computed value. Short-circuits the
      enclosing `Eff.runFunction`. -/
  | retWith  : Expr → Prog
  /-- Yield a computed value as the current block's RESULT,
      without short-circuiting the enclosing function. Uses
      `Pure.pure v` (not `Eff.return v`). Used for fold body
      results and expression statements. -/
  | yieldVal : Expr → Prog
  /-- Call a top-level name. Args are pure expressions. -/
  | call     : String → List Expr → Prog
  /-- `for item in iter: body`. -/
  | forEach  : Expr → Prog → Prog
  /-- State-threading for-loop with accumulator. -/
  | forFold  : Expr → Expr → Prog → Prog
  /-- `if cond then ifT else ifF`. -/
  | branchOn : Expr → Prog → Prog → Prog
  /-- Raise an exception with a computed value. -/
  | raiseExc : Expr → Prog
  /-- `assert test, msg`. -/
  | assertStmt : Expr → Expr → Prog
  /-- `try body except handler`. -/
  | tryExc     : Prog → Prog → Prog
  /-- `while cond: body`. Fuel-bounded: runs up to 10000
      iterations, then stops. -/
  | whileBody  : Expr → Prog → Prog
  /-- `break` — exits enclosing loop. -/
  | break_     : Prog
  /-- `continue` — skips to next loop iteration. -/
  | continue_  : Prog

namespace Prog

/-- Compute the perm of a `Prog` structurally. Unlike
    `EffAST.permsOf`, this is single-function-scoped (no `FuncEnv`
    recursion yet) — Pass 1+2 handles intra-function analysis
    only. Interprocedural propagation will come with the `.call`
    case being extended to recurse into local callees. -/
def permsOf (extEnv : ExtEnv) : Prog → Perms
  | .pureStmt    => Perms.none
  | .seq a b     => Perms.union (permsOf extEnv a) (permsOf extEnv b)
  | .letIn _ k   => permsOf extEnv k
  | .letInEff e k => Perms.union (permsOf extEnv e) (permsOf extEnv k)
  | .retWith _   => Perms.none
  | .yieldVal _  => Perms.none
  | .call name _ =>
    match extEnv.find? (·.1 == name) with
    | some (_, p) => p
    | none => Perms.top
  | .forEach _ body => permsOf extEnv body
  | .forFold _ _ body => permsOf extEnv body
  | .branchOn _ t e => Perms.union (permsOf extEnv t) (permsOf extEnv e)
  | .raiseExc _ => Perms.none
  | .assertStmt _ _ => Perms.none
  | .tryExc t h => Perms.union (permsOf extEnv t) (permsOf extEnv h)
  | .whileBody _ body => permsOf extEnv body
  | .break_ => Perms.none
  | .continue_ => Perms.none

/-- Interpret a `Prog` in a given param env, producing an `Eff`
    at the exact perm computed by `permsOf`. Dependently typed. -/
def interp (extEnv : ExtEnv) (env : Env)
    : (prog : Prog) → Eff (permsOf extEnv prog) PyVal
  | .pureStmt    => Pure.pure PyVal.none
  | .seq a b     =>
    Eff.bindSub (interp extEnv env a) (fun _ => interp extEnv env b)
  | .letIn e k   => interp extEnv (env ++ [Expr.eval env e]) k
  | .letInEff e k =>
    Eff.bindSub
      (interp extEnv env e)
      (fun v => interp extEnv (env ++ [v]) k)
  | .retWith e   => Eff.return (Expr.eval env e)
  | .yieldVal e  => Pure.pure (Expr.eval env e)
  | .call name _ => by
    show Eff (match extEnv.find? (·.1 == name) with
              | some (_, p) => p
              | none => Perms.top) PyVal
    split
    case h_1 _ _ p _ =>
      exact Eff.sub (Perms.none_sub p) (Pure.pure PyVal.none)
    case h_2 _ _ =>
      exact Eff.sub (Perms.none_sub Perms.top) (Pure.pure PyVal.none)
  | .forEach iter body =>
    -- Expected type: Eff (permsOf extEnv body) PyVal.
    -- Walk the iterable, running `body` once per element with
    -- the element pushed onto the env as a fresh de-Bruijn.
    -- `pyForEach` expects `PyVal → Eff p Unit`; we discard the
    -- body's `PyVal` result to match.
    let iterVal := Expr.eval env iter
    let loopResult : Eff (Prog.permsOf extEnv body) Unit :=
      pyForEach iterVal (fun item => do
        let _ ← interp extEnv (env ++ [item]) body
        pure ())
    do
      let _ ← loopResult
      pure PyVal.none
  | .forFold iter init body =>
    -- Expected type: Eff (permsOf extEnv body) PyVal.
    -- `pyForFold` threads an accumulator through iterations.
    -- Each iteration sees `acc` at `env.length` and `item` at
    -- `env.length + 1`. The body's return value becomes the
    -- next accumulator; the loop's result is the final acc.
    let iterVal := Expr.eval env iter
    let initVal := Expr.eval env init
    pyForFold iterVal initVal (fun acc item =>
      interp extEnv (env ++ [acc, item]) body)
  | .branchOn cond t e =>
    -- Expected type: Eff (union (permsOf t) (permsOf e)) PyVal.
    -- Pick a branch by runtime truthiness, then lift that
    -- branch's Eff to the union perm via unionSubLeft/Right.
    if pyTruthy (Expr.eval env cond) then
      Eff.sub (Perms.unionSubLeft _ _) (interp extEnv env t)
    else
      Eff.sub (Perms.unionSubRight _ _) (interp extEnv env e)
  | .raiseExc e =>
    Eff.raise (Expr.eval env e)
  | .assertStmt test msg =>
    if pyTruthy (Expr.eval env test) then
      Pure.pure PyVal.none
    else
      Eff.raise (Expr.eval env msg)
  | .tryExc t h =>
    Eff.tryCatch
      (Eff.sub (Perms.unionSubLeft _ _) (interp extEnv env t))
      (fun _ => Eff.sub (Perms.unionSubRight _ _) (interp extEnv env h))
  | .whileBody cond body =>
    let condVal := Expr.eval env cond
    let loopResult : Eff (permsOf extEnv body) Unit :=
      pyWhile 10000
        (Pure.pure condVal)
        (do let _ ← interp extEnv env body; pure ())
    do let _ ← loopResult; pure PyVal.none
  | .break_ => Eff.break
  | .continue_ => Eff.continue

inductive ProgEntry where
  | regular : Prog → ProgEntry
  | closureFactory : Nat → Prog → ProgEntry

abbrev ProgEnv := List (String × ProgEntry)

/-- Fuel-bounded interpreter that actually calls functions via `progEnv`
    lookup instead of stubbing to `PyVal.none`. Returns `Eff Perms.top`
    (not dependently typed) so it can dispatch to callees at any perm
    level. Used for value-level assertions where cross-function return
    values matter. The permissions-correct `interp` is still used for
    the type-level effect verification. -/
def interpWithCalls (fuel : Nat) (extEnv : ExtEnv) (progEnv : ProgEnv) (env : Env)
    : Prog → Eff Perms.top PyVal
  | .pureStmt    => Pure.pure PyVal.none
  | .seq a b     => do
    let _ ← interpWithCalls fuel extEnv progEnv env a
    interpWithCalls fuel extEnv progEnv env b
  | .letIn e k   => interpWithCalls fuel extEnv progEnv (env ++ [Expr.eval env e]) k
  | .letInEff e k => do
    let v ← interpWithCalls fuel extEnv progEnv env e
    interpWithCalls fuel extEnv progEnv (env ++ [v]) k
  | .retWith e   => Eff.return (Expr.eval env e)
  | .yieldVal e  => Pure.pure (Expr.eval env e)
  | .call name args =>
    let argVals := args.map (Expr.eval env)
    match fuel with
    | 0 => Pure.pure PyVal.none
    | fuel + 1 =>
      match progEnv.find? (·.1 == name) with
      | some (_, .regular calleeProg) =>
        Eff.runFunction (interpWithCalls fuel extEnv progEnv argVals calleeProg)
      | some (_, .closureFactory _ innerProg) =>
        Eff.runFunction (interpWithCalls fuel extEnv progEnv argVals innerProg)
      | none => Pure.pure PyVal.none
  | .forEach iter body =>
    let iterVal := Expr.eval env iter
    do
      let _ ← pyForEach iterVal (fun item => do
        let _ ← interpWithCalls fuel extEnv progEnv (env ++ [item]) body
        pure ())
      pure PyVal.none
  | .forFold iter init body =>
    let iterVal := Expr.eval env iter
    let initVal := Expr.eval env init
    pyForFold iterVal initVal (fun acc item =>
      interpWithCalls fuel extEnv progEnv (env ++ [acc, item]) body)
  | .branchOn cond t e =>
    if pyTruthy (Expr.eval env cond) then
      interpWithCalls fuel extEnv progEnv env t
    else
      interpWithCalls fuel extEnv progEnv env e
  | .raiseExc e =>
    Eff.raise (Expr.eval env e)
  | .assertStmt test msg =>
    if pyTruthy (Expr.eval env test) then
      Pure.pure PyVal.none
    else
      Eff.raise (Expr.eval env msg)
  | .tryExc t h =>
    Eff.tryCatch
      (interpWithCalls fuel extEnv progEnv env t)
      (fun _ => interpWithCalls fuel extEnv progEnv env h)
  | .whileBody cond body =>
    let condVal := Expr.eval env cond
    do
      let _ ← pyWhile 10000
        (Pure.pure condVal)
        (do let _ ← interpWithCalls fuel extEnv progEnv env body; pure ())
      pure PyVal.none
  | .break_ => Eff.break
  | .continue_ => Eff.continue

end Prog

end EffProg

-- ============================================================================
-- First-class call graph
-- ============================================================================
--
-- The codegen has several internal fixpoint passes that walk the
-- call graph implicitly (noncomputability classification, perms
-- widening, effect inference). This module exposes the call graph
-- as a first-class data structure that the codegen ALSO emits per
-- module, so user property files can query it directly:
--
--     example : "ext_send_email" ∈ CallGraph.transitiveCallees my__cg "main" := by
--       native_decide

/-- Static call graph for a module. Each entry maps a function
    name to the names of every function it directly calls
    (externals, top-level locals, builtins). -/
structure CallGraph where
  edges : List (String × List String)
  deriving Repr, Inhabited

namespace CallGraph

/-- Direct callees of a function. Returns `[]` if the function
    isn't in the graph. -/
def callees (g : CallGraph) (name : String) : List String :=
  match g.edges.find? (·.1 == name) with
  | some (_, cs) => cs
  | none => []

/-- Direct callers of a function. -/
def callers (g : CallGraph) (name : String) : List String :=
  g.edges.filterMap fun (caller, cs) => if cs.contains name then some caller else none

/-- Transitive callees: every function reachable from `name` via
    one or more direct calls. Uses fuel-bounded DFS so it's total
    and `native_decide`-able. -/
def transitiveCalleesAux (g : CallGraph) : Nat → List String → List String → List String
  | 0, _, acc => acc
  | _+1, [], acc => acc
  | f+1, name :: rest, acc =>
    if acc.contains name then transitiveCalleesAux g f rest acc
    else
      let direct := callees g name
      let newAcc := name :: acc
      transitiveCalleesAux g f (direct ++ rest) newAcc

def transitiveCallees (g : CallGraph) (name : String) : List String :=
  let all := transitiveCalleesAux g 1024 [name] []
  all.filter (· != name)

/-- True iff `target` is transitively reachable from `name`. -/
def reaches (g : CallGraph) (name target : String) : Bool :=
  (transitiveCallees g name).contains target

/-- True iff `name` does NOT transitively reach `target`. Useful
    for negative properties like "this function never calls
    `send_email`". -/
def neverReaches (g : CallGraph) (name target : String) : Bool :=
  !(reaches g name target)

end CallGraph

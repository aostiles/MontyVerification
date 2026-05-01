import MontyVerification.EffectMonad

/-!
# Demo: hand-written verification proofs against codegen output

This file shows what verification *means* in practice on the
MontyVerification pipeline. Each section embeds a representative slice
of the codegen output for a real corpus file, then proves a Lean
theorem that says something concrete about the program. The proofs are
discharged with `decide` / `native_decide` / `rfl` — the user doesn't
write Lean by hand for these; they just choose which property to ask
about.

There are three categories:

1. **Effect-tracking proofs** (Section 1) — the type alone is the
   verification: `Eff Perms.none PyVal` for a Pure function vs
   `Eff { net := true } PyVal` for an effectful one. If the codegen
   compiles, the function actually has those effects. The proofs in
   this section are vacuous (`rfl` on the type) — but the *fact that
   the type checks* is the safety guarantee.

2. **Happy-path execution proofs** (Section 2) — the asserts in the
   Python source actually pass when the codegen-translated body runs
   to completion. We prove `«__module__».run = .ok PyVal.none`.

3. **Intentional-error proofs** (Section 3) — the Python source is a
   negative test (`1/0`, missing dict key, type mismatch). The
   asserts are *supposed* to fail; the verification is that the body
   actually evaluates to `.error (.exception _)`. We prove
   `«__module__».run ≠ .ok PyVal.none`.

These three categories together cover what the corpus measurement
script reports as 441 / 454 provable.
-/

set_option maxRecDepth 4096

namespace DemoProofs

-- ============================================================================
-- Section 1: Effect-tracking
-- ============================================================================
--
-- Source: function__effect_demo.py
--
--     def summarize(text: str) -> Pure[str]:
--         result = ''
--         for word in text.split(' '):
--             if len(result) + len(word) < 200:
--                 result = result + word + ' '
--         return result.strip()
--
--     def research_and_notify(topic: str, recipient: str) -> Effect[Net, str]:
--         raw = search_web(topic)
--         summary = summarize(raw)
--         send_email(recipient, summary)
--         return summary

def ext_search_web : PyVal → Eff { net := true } PyVal := fun _ => pure PyVal.none
def ext_send_email : PyVal → PyVal → Eff { net := true } PyVal := fun _ _ => pure PyVal.none

def summarize (text : PyVal) : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let result := (PyVal.str "")
    pyForEach text (fun (word : PyVal) => do
      let _ ← (do
        if pyTruthy (pyLt (pyAdd (pyLen result) (pyLen word)) (PyVal.int 200)) then do
          let _result := (pyAdd (pyAdd result word) (PyVal.str " "))
          pure _result
        else do
          pure PyVal.none
        : Eff Perms.none PyVal)
      pure ())
    (Eff.return result : Eff Perms.none PyVal))

def research_and_notify (topic : PyVal) (recipient : PyVal)
    : Eff { net := true } PyVal :=
  Eff.runFunction (do
    let raw ← ext_search_web topic
    -- `summarize` is `Eff Perms.none`; the surrounding context is
    -- `Eff { net := true }`. Codegen now uses `Eff.liftSub` (a
    -- `decide`-discharged sub-permission lift) for this case
    -- automatically; here we lift explicitly via the structural
    -- `⟨...run⟩` form. The lift preserves the value; it just
    -- relabels the perms index.
    let summary ← (⟨(summarize raw).run⟩ : Eff { net := true } PyVal)
    let _ ← ext_send_email recipient summary
    (Eff.return summary : Eff { net := true } PyVal))

/-- **Theorem 1.1** (effect-tracking witness). The compiler accepts this
    declaration, which is the entire content of the verification: `summarize`
    has type `Eff Perms.none PyVal`, meaning it's permitted to use no
    effects. If `summarize`'s body had called `ext_search_web` (a `Net`
    external), the type would not check and this `def` would be rejected.
    The fact that the surrounding `def` exists is the proof. -/
theorem summarize_is_pure :
    (summarize : PyVal → Eff Perms.none PyVal) = summarize := rfl

/-- **Theorem 1.2** (effect-tracking witness for an effectful function).
    `research_and_notify` declares `Eff { net := true }`. Its body uses
    `ext_search_web` and `ext_send_email`, both `Net` externals, so the
    type checks. A "Pure" annotation on the same body would be rejected
    by Lean — that's the soundness story. -/
theorem research_is_net :
    (research_and_notify : PyVal → PyVal → Eff { net := true } PyVal)
      = research_and_notify := rfl

/-- **Theorem 1.3** (the verification really lives in the type system).
    We can't write a "wrong" version of `research_and_notify` directly
    because Lean would reject it at parse time. The closest we can get
    is showing that a hand-crafted `Eff Perms.none` value can't be the
    same value as a `Eff { net := true }` one — they live in different
    types, so the equality wouldn't even type-check. The compiler
    enforces this for us at every call site. As a stand-in, we observe
    that the two `Perms` structures are concretely distinct: -/
example : ({} : Perms) ≠ { net := true } := by decide

-- ============================================================================
-- Section 2: Happy-path execution
-- ============================================================================
--
-- Source: bool__ops.py
--
--     assert (5 and 3) == 3, 'and truthy'
--     assert (0 and 3) == 0, 'and falsy'
--     ...etc...
--
-- Every assert evaluates to true, so the codegen body's `__module__.run`
-- equals `.ok PyVal.none`.

def «bool_ops_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let _ ← (if pyTruthy (pyEq (pyAnd (PyVal.int 5) (PyVal.int 3)) (PyVal.int 3))
              then pure PyVal.none
              else Eff.raise (PyVal.str "and truthy") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyAnd (PyVal.int 0) (PyVal.int 3)) (PyVal.int 0))
              then pure PyVal.none
              else Eff.raise (PyVal.str "and falsy") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyOr (PyVal.int 5) (PyVal.int 3)) (PyVal.int 5))
              then pure PyVal.none
              else Eff.raise (PyVal.str "or truthy") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyOr (PyVal.int 0) (PyVal.int 3)) (PyVal.int 3))
              then pure PyVal.none
              else Eff.raise (PyVal.str "or falsy") : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 2.1** (all asserts pass). Every top-level boolean
    operation in the source `bool__ops.py` evaluates to the value the
    assert expects, so the body short-circuits through every `if` and
    reaches the trailing `pure PyVal.none`. -/
theorem bool_ops_succeeds :
    «bool_ops_module».run = .ok PyVal.none := by rfl

/-- **Theorem 2.2** (the result is genuinely `.ok PyVal.none`, not
    just propositionally equal). Same theorem proved by `decide`,
    showing the proposition is *decidable*: Lean can compute both
    sides and check them. This is what the corpus measurement
    counts when it reports `decide` successes. -/
theorem bool_ops_decides :
    «bool_ops_module».run = .ok PyVal.none := by decide

-- ============================================================================
-- Section 3: Intentional-error witness
-- ============================================================================
--
-- Source: arith__div_zero_int.py
--
--     1 / 0
--     # Raise=ZeroDivisionError('division by zero')
--
-- The Python file is a negative test: it's *supposed* to raise. The
-- codegen lowers `1 / 0` to a call that returns `PyVal.none` (the
-- divide-by-zero placeholder); the trailing `pure PyVal.none` then
-- becomes the body's result. So `__module__.run = .ok PyVal.none`
-- is actually... true here, not false. Let's pick a more interesting
-- error case.
--
-- Source: assert__fail.py (assert that's expected to fail)
--
--     assert False, 'this is intentional'
--
-- The codegen lowers this to `Eff.raise (PyVal.str "this is intentional")`,
-- so the body returns `.error (.exception (PyVal.str "this is intentional"))`,
-- which is *not* `.ok PyVal.none`.

def «assert_fail_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let _ ← (if pyTruthy (PyVal.bool false)
              then pure PyVal.none
              else Eff.raise (PyVal.str "this is intentional")
              : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 3.1** (intentional error reaches the assert). The body
    is supposed to fail at the assert. We witness that by proving the
    body's `.run` is *not* `.ok PyVal.none` — which means it must be
    `.error _`, which is exactly what the Python source intended. -/
theorem assert_fail_actually_fails :
    «assert_fail_module».run ≠ .ok PyVal.none := by decide

/-- **Theorem 3.2** (we can also prove the *exact* error). The body
    raises with the message `"this is intentional"`, and we can prove
    that's the precise control flow. This is the kind of property
    that's only meaningful because the body actually reduces — the
    earlier "computable externals" pass is what made this work. -/
theorem assert_fail_exact :
    «assert_fail_module».run
      = .error (.exception (PyVal.str "this is intentional")) := by rfl

-- ============================================================================
-- Section 4: Combining effects and execution
-- ============================================================================
--
-- A function that *could* be effectful but happens to be reachable
-- from a Pure context with a known input. The pyForEach over an
-- empty list never enters the body, so `summarize ""` is observable
-- as returning the empty string.

/-- **Theorem 4.1** (summarize on empty input). Even though `summarize`
    has a for-loop that could do many things, on the empty input the
    loop body never runs and the result is just the empty-string
    accumulator. We prove this by `rfl` — the body fully reduces. -/
theorem summarize_empty :
    (summarize (PyVal.str "")).run = .ok (PyVal.str "") := by rfl

/-- **Theorem 4.2** (summarize on a list-shaped non-string). The
    codegen models `text.split(' ')` as iterating over `text`
    directly (a faithfulness gap), so passing a list of strings
    runs the loop once per element. We can prove the result. -/
theorem summarize_list_input :
    (summarize (PyVal.list [PyVal.str "hi"])).run
      = .ok (PyVal.str "") := by
  -- The result accumulator is initialized to "" and the first
  -- iteration computes a new result via shadowed `let _result`,
  -- but the shadowed binding doesn't escape the if-block — the
  -- outer `result` stays "". This is a known faithfulness limit
  -- of the current shadowing-via-let lowering; the proof witnesses
  -- the actual behavior.
  rfl

-- ============================================================================
-- Section 5: Arithmetic invariants
-- ============================================================================
--
-- These mirror typical "math__*" corpus files: a sequence of asserts on
-- numeric operators. The point is that the operator semantics in
-- `EffectMonad.lean` (`pyAdd`, `pyMul`, `pyFloorDiv`, `pyMod`) are
-- *honest enough* that real arithmetic identities reduce by `rfl`.

def «arith_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    -- 2 + 3 == 5
    let _ ← (if pyTruthy (pyEq (pyAdd (PyVal.int 2) (PyVal.int 3)) (PyVal.int 5))
              then pure PyVal.none
              else Eff.raise (PyVal.str "add") : Eff Perms.none PyVal)
    -- 7 * 6 == 42
    let _ ← (if pyTruthy (pyEq (pyMul (PyVal.int 7) (PyVal.int 6)) (PyVal.int 42))
              then pure PyVal.none
              else Eff.raise (PyVal.str "mul") : Eff Perms.none PyVal)
    -- (-7) // 2 == -4   (Python floor division rounds toward -∞)
    let _ ← (if pyTruthy (pyEq (pyFloorDiv (PyVal.int (-7)) (PyVal.int 2)) (PyVal.int (-4)))
              then pure PyVal.none
              else Eff.raise (PyVal.str "floordiv neg") : Eff Perms.none PyVal)
    -- (-7) % 2 == 1     (Python modulo: sign of divisor)
    let _ ← (if pyTruthy (pyEq (pyMod (PyVal.int (-7)) (PyVal.int 2)) (PyVal.int 1))
              then pure PyVal.none
              else Eff.raise (PyVal.str "mod neg") : Eff Perms.none PyVal)
    -- 2 ** 10 == 1024
    let _ ← (if pyTruthy (pyEq (pyPow (PyVal.int 2) (PyVal.int 10)) (PyVal.int 1024))
              then pure PyVal.none
              else Eff.raise (PyVal.str "pow") : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 5.1** (every arithmetic assert passes). The proposition
    holds by `decide`, which means Lean computes both sides of every
    `pyEq` and checks them. This is direct evidence that the operator
    semantics are computable, not symbolic. -/
theorem arith_decides :
    «arith_module».run = .ok PyVal.none := by decide

/-- **Theorem 5.2** (Python's negative-floor-division convention is
    actually what we implement). Standalone witness for the trickiest
    operator: `(-7) // 2 = -4`, *not* `-3` (which is what truncation
    would give). The proof is `rfl` because `pyFloorDiv` reduces. -/
theorem floor_div_neg :
    pyFloorDiv (PyVal.int (-7)) (PyVal.int 2) = PyVal.int (-4) := rfl

/-- **Theorem 5.3** (modulo sign matches the divisor, Python-style). -/
theorem mod_neg_positive_divisor :
    pyMod (PyVal.int (-7)) (PyVal.int 2) = PyVal.int 1 := rfl

/-- **Theorem 5.4** (string concatenation is `pyAdd`). The codegen lowers
    `"foo" + "bar"` to `pyAdd (PyVal.str "foo") (PyVal.str "bar")`, and
    we can prove that's literally `"foobar"`. -/
theorem string_concat :
    pyAdd (PyVal.str "foo") (PyVal.str "bar") = PyVal.str "foobar" := rfl

/-- **Theorem 5.5** (string repetition via `pyMul`). `"ab" * 3 = "ababab"`. -/
theorem string_repeat :
    pyMul (PyVal.str "ab") (PyVal.int 3) = PyVal.str "ababab" := rfl

-- ============================================================================
-- Section 6: List / dict structural equality
-- ============================================================================
--
-- The hand-written `DecidableEq PyVal` instance lets `pyEq` on
-- compound types reduce. Without it, an assert like `[1, 2, 3] == [1, 2, 3]`
-- would not reduce — `pyEq` would be stuck on the structural recursion.

def «list_eq_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let _ ← (if pyTruthy (pyEq (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3])
                               (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]))
              then pure PyVal.none
              else Eff.raise (PyVal.str "list eq") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (PyVal.dict [(PyVal.str "a", PyVal.int 1)])
                               (PyVal.dict [(PyVal.str "a", PyVal.int 1)]))
              then pure PyVal.none
              else Eff.raise (PyVal.str "dict eq") : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 6.1** (list and dict structural equality reduce). Both
    asserts pass and the body's `.run` is `.ok PyVal.none`. -/
theorem list_eq_decides :
    «list_eq_module».run = .ok PyVal.none := by decide

/-- **Theorem 6.2** (list inequality is also decidable). A negative
    case: `[1, 2] ≠ [1, 2, 3]`. -/
theorem list_neq :
    pyEq (PyVal.list [PyVal.int 1, PyVal.int 2])
         (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3])
      = PyVal.bool false := by decide

/-- **Theorem 6.3** (`pyIn` for list membership reduces). -/
theorem list_membership :
    pyIn (PyVal.int 2) (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3])
      = PyVal.bool true := by decide

-- ============================================================================
-- Section 7: Control-flow witnesses
-- ============================================================================
--
-- `Eff.runFunction` converts a pending `.returned v` back into `.ok v`,
-- and `pyForEach` catches `.broke` / `.continued`. We can prove that
-- `return` short-circuits past code that would otherwise raise, and that
-- `break` in a loop terminates iteration before its body runs forever.

def «return_short_circuit» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    -- return 42 BEFORE the failing assert
    let _ ← (Eff.return (PyVal.int 42) : Eff Perms.none PyVal)
    let _ ← (Eff.raise (PyVal.str "unreachable") : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 7.1** (early `return` short-circuits past a raise). The
    function body returns 42 before the unreachable raise. The proof
    is `rfl`: `Eff.runFunction` rewrites `.returned (PyVal.int 42)` to
    `.ok (PyVal.int 42)`. The fact that the trailing `Eff.raise` doesn't
    affect the result is the witness that `return` actually short-circuits. -/
theorem return_short_circuits :
    «return_short_circuit».run = .ok (PyVal.int 42) := rfl

def «break_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    -- Loop over [1, 2, 3]; break on first iteration before raising.
    pyForEach (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]) (fun _ => do
      let _ ← (Eff.break : Eff Perms.none PyVal)
      let _ ← (Eff.raise (PyVal.str "unreachable") : Eff Perms.none PyVal)
      pure ())
    pure PyVal.none)

/-- **Theorem 7.2** (`break` terminates a loop without running more
    iterations). If `break` were a no-op, the second statement in the
    body would raise and the result would be `.error _`. The fact that
    we get `.ok PyVal.none` is the witness. -/
theorem break_terminates_loop :
    «break_module».run = .ok PyVal.none := by decide

def «continue_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    pyForEach (PyVal.list [PyVal.int 1, PyVal.int 2]) (fun _ => do
      let _ ← (Eff.continue : Eff Perms.none PyVal)
      let _ ← (Eff.raise (PyVal.str "unreachable") : Eff Perms.none PyVal)
      pure ())
    pure PyVal.none)

/-- **Theorem 7.3** (`continue` skips the rest of an iteration). Same
    structure as the break test, but using `Eff.continue`. The loop
    completes normally because the post-`continue` raise is unreachable. -/
theorem continue_skips_iteration :
    «continue_module».run = .ok PyVal.none := by decide

-- ============================================================================
-- Section 8: Exception recovery via try/except
-- ============================================================================
--
-- `Eff.tryCatch` matches Python's `try/except`: it converts a raised
-- exception into a normal value via the handler, but lets `return`,
-- `break`, and `continue` propagate. Codegen lowers `try: ... except: ...`
-- directly to this combinator.

def «try_recovers_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    -- try: raise "boom"; except: pass; assert reached
    let _ ← (Eff.tryCatch
              (Eff.raise (PyVal.str "boom") : Eff Perms.none PyVal)
              (fun _ => pure PyVal.none) : Eff Perms.none PyVal)
    pure (PyVal.str "after"))

/-- **Theorem 8.1** (a caught exception lets execution continue). The
    raise is wrapped in a `tryCatch` whose handler ignores the value, so
    the body finishes normally with `"after"`. -/
theorem try_recovers :
    «try_recovers_module».run = .ok (PyVal.str "after") := by decide

def «try_return_propagates» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    -- try: return 99; except: pass    -- the return must escape the try
    let _ ← (Eff.tryCatch
              (Eff.return (PyVal.int 99) : Eff Perms.none PyVal)
              (fun _ => pure PyVal.none) : Eff Perms.none PyVal)
    -- This raise must NOT run, because the return short-circuits.
    let _ ← (Eff.raise (PyVal.str "unreachable") : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 8.2** (`return` inside a `try` propagates past the
    `except`). The handler is only invoked for `.exception _`, so a
    pending `.returned` flows past it unchanged and is converted by
    `Eff.runFunction`. -/
theorem try_return_propagates_thm :
    «try_return_propagates».run = .ok (PyVal.int 99) := rfl

-- ============================================================================
-- Section 9: Cross-function effect-tracking composition
-- ============================================================================
--
-- A Pure caller composing two Pure helpers. The interesting verification
-- is the *type* — `compose : Eff Perms.none PyVal` is only inhabited if
-- every callee is also `Eff Perms.none`. Replacing `add_one` with a
-- `Net`-effect external would make `compose` fail to type-check.

def add_one (x : PyVal) : Eff Perms.none PyVal :=
  Eff.runFunction (Eff.return (pyAdd x (PyVal.int 1)))

def double (x : PyVal) : Eff Perms.none PyVal :=
  Eff.runFunction (Eff.return (pyMul x (PyVal.int 2)))

def compose (x : PyVal) : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let y ← add_one x
    let z ← double y
    (Eff.return z : Eff Perms.none PyVal))

/-- **Theorem 9.1** (composition of pure functions is itself pure, and
    the result reduces). `compose 5 = double (add_one 5) = (5+1)*2 = 12`,
    proved by `rfl`. The fact that the `def compose` exists with type
    `Eff Perms.none` is the effect-tracking witness; the value-equality
    is the additional execution witness. -/
theorem compose_pure :
    (compose (PyVal.int 5)).run = .ok (PyVal.int 12) := rfl

/-- **Theorem 9.2** (the pure composition really lives at `Perms.none`).
    Type-level witness analogous to Theorem 1.1. If any of `add_one`,
    `double`, or `compose` had snuck a `Net` external in, this `def`
    would be rejected at compile time. -/
theorem compose_is_pure :
    (compose : PyVal → Eff Perms.none PyVal) = compose := rfl

-- ============================================================================
-- Section 10: Exact-error witnesses
-- ============================================================================
--
-- Section 3 proved an intentional failure reaches its assert. Here we
-- prove the *exact* exception value for several common patterns: an
-- assert with a custom message, a raise of a string, and a raise inside
-- a function returning to the caller.

def «assert_with_msg» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let _ ← (if pyTruthy (pyEq (PyVal.int 1) (PyVal.int 2))
              then pure PyVal.none
              else Eff.raise (PyVal.str "1 should equal 2")
              : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 10.1** (exact assert message). The body raises with the
    user-supplied assert message, and we can prove the run produces
    exactly that error value. -/
theorem assert_msg_exact :
    «assert_with_msg».run
      = .error (.exception (PyVal.str "1 should equal 2")) := rfl

def raise_in_callee : Eff Perms.none PyVal :=
  Eff.runFunction (Eff.raise (PyVal.str "from callee"))

def «caller_propagates» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let _ ← raise_in_callee
    pure PyVal.none)

/-- **Theorem 10.2** (raised exception in callee propagates to caller
    with its value intact). The caller doesn't catch it, so the value
    `"from callee"` flows out unchanged. This is the witness that
    `Eff.bind`'s short-circuit on `.error` actually preserves the
    exception payload. -/
theorem callee_raise_propagates :
    «caller_propagates».run
      = .error (.exception (PyVal.str "from callee")) := rfl

-- ============================================================================
-- Section 11: Built-in functions
-- ============================================================================
--
-- Codegen now dispatches `len(x)`, `abs(x)`, `min(a, b)`, `max(a, b)`,
-- `sum(xs)`, `str(x)`, `int(x)`, `bool(x)`, `divmod(a, b)`, etc. into
-- real `pyLen` / `pyAbs` / `pyMin2` / ... helpers in `EffectMonad.lean`,
-- so assertions about builtin return values now reduce concretely
-- instead of being vacuous against `PyVal.none`. This section witnesses
-- the most common ones.

def «builtins_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    -- len([1, 2, 3]) == 3
    let _ ← (if pyTruthy (pyEq (pyLen (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]))
                                (PyVal.int 3))
              then pure PyVal.none
              else Eff.raise (PyVal.str "len list") : Eff Perms.none PyVal)
    -- len("hello") == 5
    let _ ← (if pyTruthy (pyEq (pyLen (PyVal.str "hello")) (PyVal.int 5))
              then pure PyVal.none
              else Eff.raise (PyVal.str "len str") : Eff Perms.none PyVal)
    -- abs(-7) == 7
    let _ ← (if pyTruthy (pyEq (pyAbs (PyVal.int (-7))) (PyVal.int 7))
              then pure PyVal.none
              else Eff.raise (PyVal.str "abs neg") : Eff Perms.none PyVal)
    -- min(3, 5) == 3
    let _ ← (if pyTruthy (pyEq (pyMin2 (PyVal.int 3) (PyVal.int 5)) (PyVal.int 3))
              then pure PyVal.none
              else Eff.raise (PyVal.str "min2") : Eff Perms.none PyVal)
    -- max(3, 5) == 5
    let _ ← (if pyTruthy (pyEq (pyMax2 (PyVal.int 3) (PyVal.int 5)) (PyVal.int 5))
              then pure PyVal.none
              else Eff.raise (PyVal.str "max2") : Eff Perms.none PyVal)
    -- sum([1, 2, 3, 4]) == 10
    let _ ← (if pyTruthy (pyEq (pySumIter (PyVal.list [PyVal.int 1, PyVal.int 2,
                                                          PyVal.int 3, PyVal.int 4]))
                                (PyVal.int 10))
              then pure PyVal.none
              else Eff.raise (PyVal.str "sum") : Eff Perms.none PyVal)
    -- min([4, 1, 3, 2]) == 1
    let _ ← (if pyTruthy (pyEq (pyMinIter (PyVal.list [PyVal.int 4, PyVal.int 1,
                                                          PyVal.int 3, PyVal.int 2]))
                                (PyVal.int 1))
              then pure PyVal.none
              else Eff.raise (PyVal.str "min iter") : Eff Perms.none PyVal)
    -- max([4, 1, 3, 2]) == 4
    let _ ← (if pyTruthy (pyEq (pyMaxIter (PyVal.list [PyVal.int 4, PyVal.int 1,
                                                          PyVal.int 3, PyVal.int 2]))
                                (PyVal.int 4))
              then pure PyVal.none
              else Eff.raise (PyVal.str "max iter") : Eff Perms.none PyVal)
    -- str(42) == "42"
    let _ ← (if pyTruthy (pyEq (pyStr (PyVal.int 42)) (PyVal.str "42"))
              then pure PyVal.none
              else Eff.raise (PyVal.str "str of int") : Eff Perms.none PyVal)
    -- int("123") == 123
    let _ ← (if pyTruthy (pyEq (pyInt (PyVal.str "123")) (PyVal.int 123))
              then pure PyVal.none
              else Eff.raise (PyVal.str "int of str") : Eff Perms.none PyVal)
    -- bool(0) == False
    let _ ← (if pyTruthy (pyEq (pyBool (PyVal.int 0)) (PyVal.bool false))
              then pure PyVal.none
              else Eff.raise (PyVal.str "bool of 0") : Eff Perms.none PyVal)
    -- bool([1]) == True
    let _ ← (if pyTruthy (pyEq (pyBool (PyVal.list [PyVal.int 1])) (PyVal.bool true))
              then pure PyVal.none
              else Eff.raise (PyVal.str "bool of nonempty list") : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 11.1** (every builtin assert reduces and passes). The
    body's `.run` is `.ok PyVal.none`, witnessing that `pyLen`,
    `pyAbs`, `pyMin2`/`pyMax2`, `pySumIter`/`pyMinIter`/`pyMaxIter`,
    `pyStr`, `pyInt`, and `pyBool` all reduce to the values Python
    would produce. Before the "computable builtins" pass these
    assertions would have been vacuous against a `PyVal.none`
    placeholder. -/
theorem builtins_decides :
    «builtins_module».run = .ok PyVal.none := by native_decide

/-- **Theorem 11.2** (`divmod(7, 3) == (2, 1)`). The two-arg builtin
    `divmod` lowers to `pyDivmod`, which packs floor-div and mod into
    a tuple. -/
theorem divmod_seven_three :
    pyDivmod (PyVal.int 7) (PyVal.int 3)
      = PyVal.tuple [PyVal.int 2, PyVal.int 1] := rfl

/-- **Theorem 11.3** (`sorted([3, 1, 2]) == [1, 2, 3]`). `pySorted`
    reduces fully on a literal list because `List.mergeSort` is
    computable and the comparator (`pyLt`-derived) is decidable
    on integers. -/
theorem sorted_three :
    pySorted (PyVal.list [PyVal.int 3, PyVal.int 1, PyVal.int 2])
      = PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3] := by native_decide

/-- **Theorem 11.4** (`type(42).__name__ == "int"`). The runtime-type
    builtin returns a string tag matching CPython's `__name__`. -/
theorem type_of_int :
    pyType (PyVal.int 42) = PyVal.str "int" := rfl

-- ============================================================================
-- Section 12: Iteration builtins (range / enumerate / zip / any / all)
-- ============================================================================

/-- **Theorem 12.1** (`range(5) == [0, 1, 2, 3, 4]`). The 1-arg form of
    `range` builds a Lean `List PyVal` from `List.range`. -/
theorem range_5 :
    pyRange1 (PyVal.int 5)
      = PyVal.list [PyVal.int 0, PyVal.int 1, PyVal.int 2, PyVal.int 3, PyVal.int 4] := rfl

/-- **Theorem 12.2** (`range(2, 6) == [2, 3, 4, 5]`). The 2-arg form. -/
theorem range_2_6 :
    pyRange2 (PyVal.int 2) (PyVal.int 6)
      = PyVal.list [PyVal.int 2, PyVal.int 3, PyVal.int 4, PyVal.int 5] := rfl

/-- **Theorem 12.3** (`range(0, 10, 3) == [0, 3, 6, 9]`). The 3-arg
    form, exercising the step parameter. -/
theorem range_step_3 :
    pyRange3 (PyVal.int 0) (PyVal.int 10) (PyVal.int 3)
      = PyVal.list [PyVal.int 0, PyVal.int 3, PyVal.int 6, PyVal.int 9] := by native_decide

/-- **Theorem 12.4** (`enumerate(["a", "b"]) == [(0, "a"), (1, "b")]`). -/
theorem enumerate_two :
    pyEnumerate (PyVal.list [PyVal.str "a", PyVal.str "b"])
      = PyVal.list [PyVal.tuple [PyVal.int 0, PyVal.str "a"],
                    PyVal.tuple [PyVal.int 1, PyVal.str "b"]] := rfl

/-- **Theorem 12.5** (`zip([1,2], [3,4]) == [(1,3), (2,4)]`). -/
theorem zip_two :
    pyZip (PyVal.list [PyVal.int 1, PyVal.int 2])
          (PyVal.list [PyVal.int 3, PyVal.int 4])
      = PyVal.list [PyVal.tuple [PyVal.int 1, PyVal.int 3],
                    PyVal.tuple [PyVal.int 2, PyVal.int 4]] := rfl

/-- **Theorem 12.6** (`any([0, 0, 1]) == True`, `all([1, 1, 0]) == False`). -/
theorem any_all :
    pyAny (PyVal.list [PyVal.int 0, PyVal.int 0, PyVal.int 1]) = PyVal.bool true ∧
    pyAll (PyVal.list [PyVal.int 1, PyVal.int 1, PyVal.int 0]) = PyVal.bool false := by
  decide

-- ============================================================================
-- Section 13: String / dict method dispatch
-- ============================================================================
--
-- The codegen now dispatches `obj.method(args)` for the most common
-- string and dict methods to real `pyStr*` / `pyDict*` helpers. These
-- assertions exercise the dispatch end-to-end.

def «string_methods_module» : Eff Perms.none PyVal :=
  Eff.runFunction (do
    let _ ← (if pyTruthy (pyEq (pyStrUpper (PyVal.str "hello")) (PyVal.str "HELLO"))
              then pure PyVal.none
              else Eff.raise (PyVal.str "upper") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyStrLower (PyVal.str "WORLD")) (PyVal.str "world"))
              then pure PyVal.none
              else Eff.raise (PyVal.str "lower") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyStrStrip (PyVal.str "  hi  ")) (PyVal.str "hi"))
              then pure PyVal.none
              else Eff.raise (PyVal.str "strip") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyStrStartsWith (PyVal.str "foobar") (PyVal.str "foo"))
                                (PyVal.bool true))
              then pure PyVal.none
              else Eff.raise (PyVal.str "startswith") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyStrEndsWith (PyVal.str "foobar") (PyVal.str "bar"))
                                (PyVal.bool true))
              then pure PyVal.none
              else Eff.raise (PyVal.str "endswith") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyStrReplace (PyVal.str "abc") (PyVal.str "b") (PyVal.str "X"))
                                (PyVal.str "aXc"))
              then pure PyVal.none
              else Eff.raise (PyVal.str "replace") : Eff Perms.none PyVal)
    let _ ← (if pyTruthy (pyEq (pyStrJoinMethod (PyVal.str ", ")
                                  (PyVal.list [PyVal.str "a", PyVal.str "b", PyVal.str "c"]))
                                (PyVal.str "a, b, c"))
              then pure PyVal.none
              else Eff.raise (PyVal.str "join") : Eff Perms.none PyVal)
    pure PyVal.none)

/-- **Theorem 13.1** (every string-method assert reduces and passes). -/
theorem string_methods_decides :
    «string_methods_module».run = .ok PyVal.none := by native_decide

/-- **Theorem 13.2** (`d.get(k)` on a present key, then a missing key
    with default). Mirrors Python's `dict.get` two-arg form. -/
theorem dict_get :
    pyDictGet (PyVal.dict [(PyVal.str "a", PyVal.int 1)])
              (PyVal.str "a")
      = PyVal.int 1 ∧
    pyDictGetDefault (PyVal.dict [(PyVal.str "a", PyVal.int 1)])
                     (PyVal.str "missing")
                     (PyVal.int 99)
      = PyVal.int 99 := by
  decide

/-- **Theorem 13.3** (`d.keys()` / `d.values()` / `d.items()` reduce
    to the expected projections). -/
theorem dict_views :
    pyDictKeys (PyVal.dict [(PyVal.str "a", PyVal.int 1), (PyVal.str "b", PyVal.int 2)])
      = PyVal.list [PyVal.str "a", PyVal.str "b"] ∧
    pyDictValues (PyVal.dict [(PyVal.str "a", PyVal.int 1), (PyVal.str "b", PyVal.int 2)])
      = PyVal.list [PyVal.int 1, PyVal.int 2] := by
  decide

-- ============================================================================
-- Section 14: Closure factories (Path 1)
-- ============================================================================
--
-- Source pattern: a Python function whose body defines an inner function
-- and returns it.
--
--     def make_adder(x):
--         def add(y):
--             return x + y
--         return add
--
--     add5 = make_adder(5)
--     assert add5(3) == 8
--
-- Codegen lowers `make_adder` as `Eff Perms.none (PyClosure Perms.none 1)`
-- (returning a typed closure value), and the call site dispatches via
-- `PyClosure.call1`. The factory + call chain is fully reducible, so we
-- can prove `add5(3) = 8` by `rfl`.

def make_adder (x : PyVal) : Eff Perms.none (PyClosure Perms.none 1) := do
  pure (PyClosure.mk1 (fun (y : PyVal) => Eff.runFunction (do
    (Eff.return (pyAdd x y) : Eff Perms.none PyVal))))

/-- **Theorem 14.1** (closure factory + immediate application reduces by
    `rfl`). The chain `make_adder(5) >>= (·.call1 3)` runs to `8`. This
    is the end-to-end witness that Path 1's typed closure dispatch
    actually preserves the captured value. -/
theorem make_adder_5_then_3 :
    ((make_adder (PyVal.int 5)).bind (fun cb => PyClosure.call1 cb (PyVal.int 3))).run
      = .ok (PyVal.int 8) := by native_decide

/-- **Theorem 14.2** (calling the same factory twice gives independent
    closures). Each `make_adder` invocation builds a fresh `PyClosure`
    that captures its own `x`, so `add5(3) = 8` and `add10(3) = 13`
    don't interfere. -/
theorem make_adder_independent_calls :
    (do
      let add5 ← make_adder (PyVal.int 5)
      let add10 ← make_adder (PyVal.int 10)
      let r1 ← PyClosure.call1 add5 (PyVal.int 3)
      let r2 ← PyClosure.call1 add10 (PyVal.int 3)
      pure (PyVal.tuple [r1, r2])
      : Eff Perms.none PyVal).run
      = .ok (PyVal.tuple [PyVal.int 8, PyVal.int 13]) := by native_decide

/-- **Theorem 14.3** (closure factories preserve effect tracking).
    A factory whose inner function is pure has type
    `Eff p (PyClosure Perms.none n)` — the inner closure carries
    `Perms.none` in its index, so any caller that uses the closure
    must also accept (or strengthen to) `Perms.none`. The fact that
    this `def` exists is the witness. -/
theorem make_adder_inner_is_pure :
    (make_adder : PyVal → Eff Perms.none (PyClosure Perms.none 1))
      = make_adder := rfl

-- ============================================================================
-- Section 15: Async functions and `await` (Extension B)
-- ============================================================================
--
-- Source pattern:
--
--     async def foo():
--         return 42
--
--     async def bar(x):
--         return x * 2
--
--     result = await foo()
--     assert result == 42
--
-- Codegen lowers `async def foo` as a constructor returning a
-- `PyClosure 0` thunk that closes over the function's parameters. The
-- `await` flatten case binds the thunk and runs it via
-- `PyClosure.call0`, so the body's value flows back to the caller.

def foo_async : Eff Perms.none (PyClosure Perms.none 0) := do
  pure (PyClosure.mk0 (fun (_ : Unit) => Eff.runFunction (do
    (Eff.return (PyVal.int 42) : Eff Perms.none PyVal))))

def bar_async (x : PyVal) : Eff Perms.none (PyClosure Perms.none 0) := do
  pure (PyClosure.mk0 (fun (_ : Unit) => Eff.runFunction (do
    (Eff.return (pyMul x (PyVal.int 2)) : Eff Perms.none PyVal))))

/-- **Theorem 15.1** (`await foo() == 42` reduces by `native_decide`).
    The async function `foo` lowers as a 0-arg thunk, and `await foo()`
    binds it then calls `PyClosure.call0`. The whole chain is
    computable, so the awaited value flows through the assertion. -/
theorem await_foo_returns_42 :
    (foo_async.bind PyClosure.call0).run = .ok (PyVal.int 42) := by native_decide

/-- **Theorem 15.2** (`await bar(7) == 14`). Async function with an
    argument: `bar`'s thunk closes over the parameter, and the awaited
    body runs `x * 2`. -/
theorem await_bar_7_returns_14 :
    ((bar_async (PyVal.int 7)).bind PyClosure.call0).run
      = .ok (PyVal.int 14) := by native_decide

/-- **Theorem 15.3** (store-then-await). Bind the coroutine to a name
    first, then await it later — equivalent to `c = foo(); result = await c`.
    The closure value flows through the let-binding and the await
    recovers it correctly. The `Eff.runFunction` wrapper unpacks the
    `Eff.return` short-circuit at the synthetic function boundary,
    matching what real codegen output produces. -/
theorem store_then_await :
    (Eff.runFunction (do
      let c ← foo_async
      let result ← PyClosure.call0 c
      (Eff.return result : Eff Perms.none PyVal))).run
      = .ok (PyVal.int 42) := by native_decide

-- ============================================================================
-- Section 16: `asyncio.gather` result-shape theorem (Extension A)
-- ============================================================================
--
-- Source:
--
--     async def task1(): return 1
--     async def task2(): return 2
--     result = await asyncio.gather(task1(), task2())
--     assert result == [1, 2]
--
-- Codegen unfolds `asyncio.gather(...)` into a sequence of
-- coroutine-then-call0 bindings, then collects the awaited values
-- into a `PyVal.list`. The result has the same length and order as
-- the input arguments, which lets us prove a shape theorem.

def task1_async : Eff Perms.none (PyClosure Perms.none 0) := do
  pure (PyClosure.mk0 (fun (_ : Unit) => Eff.runFunction (do
    (Eff.return (PyVal.int 1) : Eff Perms.none PyVal))))

def task2_async : Eff Perms.none (PyClosure Perms.none 0) := do
  pure (PyClosure.mk0 (fun (_ : Unit) => Eff.runFunction (do
    (Eff.return (PyVal.int 2) : Eff Perms.none PyVal))))

def task3_async : Eff Perms.none (PyClosure Perms.none 0) := do
  pure (PyClosure.mk0 (fun (_ : Unit) => Eff.runFunction (do
    (Eff.return (PyVal.int 3) : Eff Perms.none PyVal))))

/-- **Theorem 16.1** (`gather` returns results in argument order). The
    codegen for `asyncio.gather(task1(), task2(), task3())` runs each
    coroutine and collects results into a list. We prove the
    end-to-end value is `[1, 2, 3]` — same order, same length. -/
theorem gather_three_returns_in_order :
    (Eff.runFunction (do
      let _coro0 ← task1_async
      let _res0 ← PyClosure.call0 _coro0
      let _coro1 ← task2_async
      let _res1 ← PyClosure.call0 _coro1
      let _coro2 ← task3_async
      let _res2 ← PyClosure.call0 _coro2
      (Eff.return (PyVal.list [_res0, _res1, _res2]) : Eff Perms.none PyVal))).run
      = .ok (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]) := by native_decide

/-- **Theorem 16.2** (gather of pure thunks is itself pure). The whole
    chain has type `Eff Perms.none PyVal` because every coroutine has
    `PyClosure Perms.none 0`. If any task introduced a `Net` effect,
    the type would be `Eff { net := true }` and any caller would have
    to accept that. -/
theorem gather_three_is_pure :
    let prog : Eff Perms.none PyVal := do
      let c1 ← task1_async
      let r1 ← PyClosure.call0 c1
      let c2 ← task2_async
      let r2 ← PyClosure.call0 c2
      pure (PyVal.list [r1, r2])
    prog.run = .ok (PyVal.list [PyVal.int 1, PyVal.int 2]) := by native_decide

-- ============================================================================
-- Section 17: Slice and chain comparison
-- ============================================================================
--
-- Both lowering paths fixed in the most recent round: `obj[a:b:c]` now
-- dispatches to `pySlice`, and `a < b < c` builds the `pyAnd` chain
-- correctly even on the flatten path.

/-- **Theorem 17.1** (basic list slice). `[0,1,2,3,4,5][1:4] == [1,2,3]`
    decides directly. Before the fix this was `pyIndex obj PyVal.none =
    PyVal.none`, which made the assertion vacuously false. -/
theorem slice_basic :
    pySlice (PyVal.list [PyVal.int 0, PyVal.int 1, PyVal.int 2,
                          PyVal.int 3, PyVal.int 4, PyVal.int 5])
            (PyVal.int 1) (PyVal.int 4) PyVal.none
      = PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3] := by decide

/-- **Theorem 17.2** (negative indices wrap from the end).
    `[0,1,2,3,4,5][-3:] == [3,4,5]`. -/
theorem slice_negative_start :
    pySlice (PyVal.list [PyVal.int 0, PyVal.int 1, PyVal.int 2,
                          PyVal.int 3, PyVal.int 4, PyVal.int 5])
            (PyVal.int (-3)) PyVal.none PyVal.none
      = PyVal.list [PyVal.int 3, PyVal.int 4, PyVal.int 5] := by decide

/-- **Theorem 17.3** (reverse with `step = -1`). `[0,1,2,3,4,5][::-1]
    == [5,4,3,2,1,0]`. The non-trivial step path is exercised. -/
theorem slice_reverse :
    pySlice (PyVal.list [PyVal.int 0, PyVal.int 1, PyVal.int 2,
                          PyVal.int 3, PyVal.int 4, PyVal.int 5])
            PyVal.none PyVal.none (PyVal.int (-1))
      = PyVal.list [PyVal.int 5, PyVal.int 4, PyVal.int 3,
                     PyVal.int 2, PyVal.int 1, PyVal.int 0] := by decide

/-- **Theorem 17.4** (`1 < 2 < 3` is true). Chain comparison via the
    `pyAnd (pyLt _ _) (pyLt _ _)` shape that the codegen now emits on
    both flatten and pure paths. -/
theorem chain_lt_lt :
    pyAnd (pyLt (PyVal.int 1) (PyVal.int 2)) (pyLt (PyVal.int 2) (PyVal.int 3))
      = PyVal.bool true := by decide

/-- **Theorem 17.5** (`1 < 3 < 2` is false — fails at the second link).
    The chain short-circuits: `pyAnd true false = false`. -/
theorem chain_fails_at_second :
    pyAnd (pyLt (PyVal.int 1) (PyVal.int 3)) (pyLt (PyVal.int 3) (PyVal.int 2))
      = PyVal.bool false := by decide

-- ============================================================================
-- Section 18: Multi-generator comprehensions
-- ============================================================================
--
-- Source: `[x + y for x in [1, 2] for y in [10, 20]]`
--
-- Codegen now dispatches 2-generator comprehensions to `pyListComp2`,
-- which runs the inner generator once per outer iteration. Without
-- this, the inner generator was silently dropped and the result was
-- always `PyVal.none`.

/-- **Theorem 18.1** (`[x + y for x in [1, 2] for y in [10, 20]]
    == [11, 21, 12, 22]`). The inner generator runs in full for each
    outer element, in argument order. -/
theorem listcomp2_addition :
    (pyListComp2 (p := Perms.none)
        (PyVal.list [PyVal.int 1, PyVal.int 2])
        (fun (_x : PyVal) => pure (PyVal.list [PyVal.int 10, PyVal.int 20]))
        (fun (x : PyVal) (y : PyVal) => pure (pyAdd x y))
        (fun (_x : PyVal) (_y : PyVal) => pure (PyVal.bool true))).run
      = .ok (PyVal.list [PyVal.int 11, PyVal.int 21,
                          PyVal.int 12, PyVal.int 22]) := by native_decide

/-- **Theorem 18.2** (inner generator can mention the outer variable).
    `[y for x in [[1,2], [3]] for y in x]` flattens nested lists.
    The inner-iter closure receives `x` and returns `x` itself as
    the iterable. -/
theorem listcomp2_flatten :
    (pyListComp2 (p := Perms.none)
        (PyVal.list [PyVal.list [PyVal.int 1, PyVal.int 2],
                      PyVal.list [PyVal.int 3]])
        (fun (x : PyVal) => pure x)
        (fun (_x : PyVal) (y : PyVal) => pure y)
        (fun (_x : PyVal) (_y : PyVal) => pure (PyVal.bool true))).run
      = .ok (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]) := by native_decide

-- ============================================================================
-- Section 19: Sub-permission lift via `Eff.liftSub`
-- ============================================================================
--
-- A `Net` function calling a `Pure` helper now type-checks via the
-- `decide`-discharged `Eff.liftSub`. We can witness both directions
-- of the soundness story: the lift that *should* succeed does, and
-- the one that *shouldn't* fails the `decide` proof.

def pure_helper (x : PyVal) : Eff Perms.none PyVal :=
  Eff.runFunction (Eff.return (pyMul x (PyVal.int 2)) : Eff Perms.none PyVal)

def net_caller (x : PyVal) : Eff { net := true } PyVal :=
  Eff.runFunction (do
    -- Codegen would emit `← Eff.liftSub (pure_helper x)` here. The
    -- `decide` default discharges `Perms.none.sub { net := true }`.
    let doubled ← Eff.liftSub (pure_helper x)
    (Eff.return doubled : Eff { net := true } PyVal))

/-- **Theorem 19.1** (`Net` function computes the value of its `Pure`
    helper). The lift is value-preserving — it just relabels the perms
    index — so `net_caller 21 = 42`. -/
theorem net_caller_lifts_pure :
    (net_caller (PyVal.int 21)).run = .ok (PyVal.int 42) := by native_decide

/-- **Theorem 19.2** (the lift's perms relation is decidable, and the
    safe direction is provable). Sub-permission lifts go from a
    less-permissive context to a more-permissive one; the proof
    obligation is `Perms.none.sub { net := true }`, which `decide`
    accepts. -/
theorem pure_sub_net : Perms.sub Perms.none { net := true } := by decide

/-- **Theorem 19.3** (the unsafe direction is rejected). The reverse
    relation `{ net := true }.sub Perms.none` is false — a `Net`
    computation can't be lifted into a `Pure` context. `decide`
    refutes it, which is the soundness witness for why
    `Eff.liftSub` can't be misused. -/
theorem net_not_sub_pure : ¬ Perms.sub { net := true } Perms.none := by decide

end DemoProofs

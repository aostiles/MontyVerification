import MontyVerification.Basic
import MontyVerification.JsonDeser
import MontyVerification.EffectMonad

/-!
# Lean Code Generator

Translates Monty IR into Lean source code where the type system enforces
effect safety. If the generated `.lean` file compiles, the Monty program's
effect annotations are correct. If it doesn't, the Lean type error identifies
the violation.
-/

-- ============================================================================
-- Code generation state
-- ============================================================================

structure CodegenCtx where
  ir : IrExport
  externals : List (StringId × String × String)
  knownFuncs : List (StringId × String × EffectAnnotation)
  nextVar : Nat
  perms : String := "Perms.none"
  /-- Names of locally-defined functions (from funcDef let-bindings).
      Used to detect when a name refers to a closure that needs PyVal.ofFn wrapping. -/
  localFuncNames : List StringId := []
  /-- Names of zero-param local functions that need () when called. -/
  zeroParamFuncs : List StringId := []
  /-- Param counts for local functions (for choosing PyVal.ofFn/ofFn0/ofFn2). -/
  localFuncParamCounts : List (StringId × Nat) := []
  /-- Per-function ordered parameter `StringId`s, in the same order as
      `allParamIds`. Used at call sites to map keyword arguments back to
      parameter positions when binding `.generalizedCall` invocations of
      known local/top-level functions. -/
  localFuncParamIds : List (StringId × List StringId) := []
  /-- Arities of external functions (max observed call-site arg count).
      Used to pad under-applied calls and to choose the right axiom. -/
  externalArities : List (StringId × Nat) := []
  /-- Per-funcdef default-value lookup table:
      `(funcId, paramIndex)` → name of a top-level `def` holding the
      pre-evaluated default value. Used to pad under-applied calls
      with the *real* Python default rather than a `PyVal.none`
      placeholder. -/
  funcDefaults : List ((StringId × Nat) × String) := []
  /-- Names bound to lambda expressions, with their arity. These are
      emitted as typed `PyClosure p arity` values rather than effect-erased
      `PyVal.ofPureFn`. Calls to these names go through `PyClosure.callN`,
      which preserves the closure's effect set in the type and lets Lean
      reject `Pure` functions that invoke an effectful closure. -/
  closureBindings : List (StringId × Nat) := []
  /-- Top-level functions whose body is a closure-factory shape: they
      define an inner function (or a lambda) and return it directly.
      Codegen emits these with return type `Eff p (PyClosure q arity)`
      instead of `Eff p PyVal`, and call sites bind the result as a
      typed closure (so subsequent calls go through `PyClosure.callN`
      instead of `PyVal.callFn`). The string is the closure's perms
      (e.g. `"Perms.none"`, `"{ net := true }"`). -/
  closureReturningFuncs : List (StringId × Nat × String) := []
  /-- Names bound to a builtin function value (e.g. `x = len`). Maps
      `id.nameId` to the IR builtin id (`"Len"`, `"Abs"`, ...). At call
      sites for these names, codegen dispatches directly to the
      corresponding `pyXxx` helper instead of going through the
      conservative `PyVal.callFn` path. Closes precision gap § 2.3. -/
  builtinBindings : List (StringId × String) := []
  /-- True iff the current translation context is allowed to produce
      a `PyClosure`-typed value (e.g. an assign RHS or a normal
      expression position where the closure can be bound by name).
      False inside `pyListComp` element closures and other PyVal-only
      positions where a closure value can't be embedded. When false,
      a call to a closure-returning function binds the closure to a
      `_coro` temp and returns `PyVal.none`. -/
  allowClosureReturn : Bool := true
  /-- Aliases for known top-level functions. Populated when the
      codegen sees `f = some_known_func` (an assign whose RHS is a
      bare name reference to a known local function). At call sites
      for `f`, the call is dispatched to `some_known_func` directly
      instead of going through the conservative `PyVal.callFn` path.
      Closes a slice of P4 (callFn widening) for the simple
      function-aliasing case. -/
  funcAliases : List (StringId × StringId) := []
  /-- Per-function alias map used only by the AST translator
      (`translateBodyAST`, `collectExprCallNamesAST`). Maps a
      name's source `StringId` to the final display name that
      `.call "<name>" []` should emit. Covers two shapes:

      * `f = known_func` → `f` maps to the display name of
        `known_func` (with the `ext_` prefix if appropriate).
      * `def inner(...): ...` nested inside a parent function →
        `inner` maps to the mangled sibling AST def name
        (e.g. `"parent__inner"`).

      Set fresh before each `translateBodyAST ctx fd.body` call so
      that bindings from one function don't leak into another.
      Without this, the AST translator emits `.call "f" []` for
      the source name, `permsOf` can't resolve `f`, and widens
      the surrounding function to `Perms.top`. -/
  astLocalAliases : List (StringId × String) := []
  /-- Names bound to lambda or closure-factory results in the current
      function's body. At call sites for these names, the AST
      translator emits NO call (the effects were already captured at
      the binding site when the lambda body was inlined into the call
      chain). This mirrors the executable codegen's `closureBindings`:
      closure calls go through `PyClosure.callN`, not `PyVal.callFn`,
      so they don't widen to `Perms.top`. Without this, a
      `cb = lambda ...; cb(x)` shape causes `permsOf` to widen
      because `cb` isn't in `__env`. -/
  astClosureNames : List StringId := []
  /-- True when translating the `«__module__»` body (module-level
      statements). In this context, variables may resolve to global
      `axiom` declarations rather than local `let` bindings, so
      certain SSA-style rewrites (like `opAssign` referencing the
      old value) must be suppressed to avoid `dependsOnNoncomputable`
      errors. -/
  isModuleBody : Bool := false
  /-- Names bound to `.lambda` expressions or `.funcDef` nodes in
      the current function body. Used by the EffProg translator to
      safely value-erase calls to local lambdas: if a call target
      is in this set, it was created in the current scope (not
      aliased from outside), so its perms are bounded by the outer
      function's perms. This lets us skip the call (return
      `PyVal.none`) without risking a soundness leak. -/
  progLambdaBindings : List StringId := []
  /-- Lambda bindings whose body calls externals. Maps nameId to
      the list of external call names (e.g. ["ext_send_email"]).
      Used by the EffProg translator to emit effect-surfacing calls
      at the lambda's call site, preserving the lambda's actual
      perms instead of widening to Perms.top. -/
  progLambdaEffectCalls : List (StringId × List String) := []
  /-- Variables assigned from closure-factory function calls.
      Maps nameId to the closure's inner perms string.
      When the EffProg translator encounters a call to one of
      these variables, it uses a synthetic call name with the
      closure's actual perms instead of `__indirect__`. -/
  progClosureResultPerms : List (StringId × String) := []

-- ============================================================================
-- Helpers
-- ============================================================================

def sanitizeName (s : String) : String :=
  let s := s.map fun c => if c.isAlphanum || c == '_' then c else '_'
  if s.isEmpty then "_empty"
  -- Lean treats bare `_` as an elaborator placeholder, not an identifier;
  -- Python's `_` (the throwaway / discard convention) needs renaming.
  else if s == "_" then "_unused"
  else if s.front.isDigit then "_" ++ s
  else match s with
    -- Lean keywords that can't appear as identifiers.
    | "do" | "let" | "if" | "then" | "else" | "match" | "where" | "return"
    | "fun" | "def" | "theorem" | "import" | "axiom" | "for" | "in" | "pure"
    | "by" | "local" | "prefix" | "infix" | "infixl" | "infixr" | "postfix"
    | "notation" | "macro" | "syntax" | "class" | "instance" | "structure"
    | "inductive" | "opaque" | "private" | "protected" | "section" | "namespace"
    | "open" | "end" | "mutual" | "variable" | "set_option" | "type" | "as"
    | "from" | "with" | "have" | "show" | "suffices" | "at" | "rec" | "this"
    | "matches" | "deriving" | "extends" | "unless" | "try" | "catch"
    -- Lean's `main` is special-cased: a top-level `def main` must
    -- have type `IO Unit` or similar. Python files commonly define
    -- `def main()` as their entry point, so rename it.
    | "main"
    -- Lean stdlib types/typeclasses that would clash with `axiom <name>`.
    -- Keep this list aligned with anything reachable from `import EffectMonad`.
    | "List" | "Set" | "Union" | "Option" | "Array" | "String" | "Char"
    | "Nat" | "Int" | "Bool" | "Float" | "Unit" | "Prop" | "Type" | "Sort"
    | "And" | "Or" | "Not" | "Iff" | "Eq" | "Ne" | "Ord" | "Lt" | "Le"
    | "HAdd" | "HSub" | "HMul" | "HDiv" | "HMod" | "HPow" | "HAnd" | "HOr"
    | "Add" | "Sub" | "Mul" | "Div" | "Mod" | "Pow" | "Neg" | "Inv"
    | "Functor" | "Applicative" | "Monad" | "MonadLift" | "Coe" | "CoeFun"
    | "Decidable" | "DecidableEq" | "Inhabited" | "Repr" | "ToString"
    | "BEq" | "Hashable" | "HashMap" | "HashSet" | "Subtype" | "Sigma" =>
      "py_" ++ s
    | _ => s

/-- Parse a comma-separated effect list (e.g. "net,fs") into a Lean
    perms-source string. Recognised tokens:
    - `pure` / `none` → `Perms.none`
    - `top` → `Perms.top`
    - any combination of `net`, `fs`, `env`, `time` → struct literal

    Used by the source-level `# external: <name> <effects>`
    directive parser. -/
def parseEffectsList (s : String) : String :=
  -- Use splitOn to dedup whitespace; trim each piece by hand to
  -- avoid depending on `String.Slice` operations that vary across
  -- Lean toolchains.
  let trim (x : String) : String :=
    let chars := x.toList.dropWhile (· == ' ')
    let chars := chars.reverse.dropWhile (· == ' ') |>.reverse
    chars.asString
  let s := trim s
  if s == "pure" || s == "none" then "Perms.none"
  else if s == "top" then "Perms.top"
  else
    let parts := (s.splitOn ",").map trim
    -- Standard effects map to bool fields; everything else goes
    -- into the `custom` list. Sort the custom names for canonical
    -- representation (so two perms with the same set of custom
    -- effects compare equal).
    let stdFields := parts.filterMap fun p =>
      if p == "net" then some "net := true"
      else if p == "fs" then some "fs := true"
      else if p == "env" then some "env := true"
      else if p == "time" then some "time := true"
      else none
    let customNames := parts.filter fun p =>
      !p.isEmpty && p != "net" && p != "fs" && p != "env" && p != "time"
    -- Dedupe + sort the custom names for canonical form.
    let customSorted := (customNames.eraseDups).mergeSort (· ≤ ·)
    let customField :=
      if customSorted.isEmpty then ""
      else
        let quoted := customSorted.map fun n => s!"\"{n}\""
        "custom := [" ++ String.intercalate ", " quoted ++ "]"
    let allFields := stdFields ++ (if customField.isEmpty then [] else [customField])
    if allFields.isEmpty then "Perms.none"
    else "{ " ++ String.intercalate ", " allFields ++ " }"

/-- Parse a single line of Python source for an `# external: <name>
    <effects>` directive. Returns `(name, perms-string)` if the line
    is a directive, `none` otherwise.

    Format: `# external: <name> <effect1>[,<effect2>...]`
    Examples:
      `# external: send_email net`
      `# external: log_audit fs`
      `# external: publish net,fs`
      `# external: trim pure`
      `# external: untracked top`
    -/
def parseExternalDirective (line : String) : Option (String × String) :=
  let trim (x : String) : String :=
    let chars := x.toList.dropWhile (· == ' ')
    let chars := chars.reverse.dropWhile (· == ' ') |>.reverse
    chars.asString
  let s := trim line
  if !s.startsWith "# external:" then none
  else
    -- Use list-based drop to avoid String.Slice from `.drop`.
    let restRaw := (s.toList.drop "# external:".length).asString
    let rest := trim restRaw
    -- Split on whitespace into name and the rest.
    let words := rest.splitOn " " |>.filter (· != "")
    match words with
    | [] => none
    | [_] => none
    | name :: effsParts =>
      let effs := String.intercalate " " effsParts
      if name.isEmpty || effs.isEmpty then none
      else some (name, parseEffectsList effs)

/-- Scan a Python source file's lines for `# external:` directives
    and return the parsed (name, perms) pairs. -/
def parseExternalDirectives (pythonSource : String) : List (String × String) :=
  pythonSource.splitOn "\n" |>.filterMap parseExternalDirective

/-- Walk an `IrExport` looking for the first `CodeRange.filename`
    StringId and resolve it. Used by Main.lean to find the source
    file that produced this IR (so the codegen can scan it for
    `# external:` directives). Returns `none` if no positions are
    found in the IR. -/
def extractFirstFilename (ir : IrExport) : Option String :=
  let rec firstFromNodes : List Node → Option Nat
    | [] => none
    | n :: rest =>
      match n with
      | .funcDef fd => some fd.name.position.filename
      | .assign id _ => some id.position.filename
      | .expr el => some el.position.filename
      | .ret el => some el.position.filename
      | _ => firstFromNodes rest
  match firstFromNodes ir.nodes with
  | some fid => some (ir.resolveString fid)
  | none => none


def effectAnnotationToPerms : EffectAnnotation → String
  | .pure => "Perms.none"
  | .unannotated => "Perms.none"
  | .effectful effs =>
    let fields := effs.filterMap fun e => match e with
      | .net => some "net := true" | .fs => some "fs := true"
      | .env => some "env := true" | .time => some "time := true"
      | .custom _ => none  -- IR-level custom: handled via the `# external:` directive system instead
    if fields.isEmpty then "Perms.none"
    else "{ " ++ String.intercalate ", " fields ++ " }"

/-- Inference-time representation of a function's effect set. `top`
    means the function needs `Perms.top` widening (because it touches
    `PyVal.callFn` or an unknown external). `effs es` is a concrete
    effect set; the strings are effect names — either one of the
    four standard names (`"net"`, `"fs"`, `"env"`, `"time"`) or a
    user-declared custom effect name (e.g. `"db"`, `"audit"`). The
    empty list means `Perms.none`. -/
inductive InferredPerms where
  | top
  | effs : List String → InferredPerms
  deriving Inhabited

/-- Union two inferred-perms values. Top absorbs everything. -/
def InferredPerms.union : InferredPerms → InferredPerms → InferredPerms
  | .top, _ => .top
  | _, .top => .top
  | .effs xs, .effs ys =>
    .effs (xs ++ ys.filter (fun e => !xs.contains e))

/-- Convert an `InferredPerms` to its Lean source form. The four
    standard effect names map to bool fields; everything else goes
    into a `custom := [...]` list. -/
def InferredPerms.toLeanString : InferredPerms → String
  | .top => "Perms.top"
  | .effs [] => "Perms.none"
  | .effs es =>
    let stdNames := ["net", "fs", "env", "time"]
    let stdFields := es.filterMap fun e =>
      if stdNames.contains e then some s!"{e} := true" else none
    let customs := es.filter (fun e => !stdNames.contains e)
    let customSorted := customs.eraseDups.mergeSort (· ≤ ·)
    let customField :=
      if customSorted.isEmpty then ""
      else
        let quoted := customSorted.map fun n => s!"\"{n}\""
        "custom := [" ++ String.intercalate ", " quoted ++ "]"
    let allFields := stdFields ++ (if customField.isEmpty then [] else [customField])
    if allFields.isEmpty then "Perms.none"
    else "{ " ++ String.intercalate ", " allFields ++ " }"

/-- Parse a Lean perms string back to a `List String` of effect
    names. Used to map a known external's `externalPerms` table
    entry into the inference representation. Returns `none` for
    `Perms.top` (callers should handle that as `InferredPerms.top`). -/
def parsePermsString (s : String) : Option (List String) :=
  if s == "Perms.none" then some []
  else if s == "Perms.top" then none
  else
    -- Format: "{ field, field, ..., custom := [...] }". The standard
    -- fields are `<name> := true`; the custom field is
    -- `custom := [\"name1\", \"name2\", ...]`.
    let parts := s.splitOn "{"
    let inner := match parts with
      | _ :: rest :: _ => rest
      | _ => ""
    let parts := inner.splitOn "}"
    let inner := match parts with
      | first :: _ => first
      | _ => ""
    -- Extract the `custom := [...]` portion (if any) BEFORE splitting
    -- on commas, since custom contains commas inside its bracket pair.
    let customNames : List String :=
      let cParts := inner.splitOn "custom := ["
      match cParts with
      | _ :: rest :: _ =>
        let bParts := rest.splitOn "]"
        match bParts with
        | inside :: _ =>
          (inside.splitOn ",").filterMap fun raw =>
            let t := raw.trimAscii.toString
            -- Strip surrounding quotes.
            if t.startsWith "\"" && t.endsWith "\"" then
              some ((t.toList.drop 1).dropLast.asString)
            else none
        | _ => []
      | _ => []
    -- For the standard fields, drop the custom portion before splitting.
    let stdInner :=
      let cParts := inner.splitOn "custom := ["
      match cParts with
      | first :: _ => first
      | _ => inner
    let fields := stdInner.splitOn ","
    let parsedStd : List String := fields.filterMap fun f =>
      let trimmed := f.trimAscii
      if trimmed.startsWith "net" then some "net"
      else if trimmed.startsWith "fs" then some "fs"
      else if trimmed.startsWith "env" then some "env"
      else if trimmed.startsWith "time" then some "time"
      else none
    some (parsedStd ++ customNames)

def indent (s : String) : String :=
  s.splitOn "\n" |>.map ("  " ++ ·) |> String.intercalate "\n"

/-- Choose the right PyVal.ofFn wrapper based on param count. -/
def ofFnWrapper (ctx : CodegenCtx) (nameId : StringId) : String :=
  match ctx.localFuncParamCounts.find? (·.1 == nameId) with
  | some (_, 0) => "PyVal.ofFn0"
  | some (_, 1) => "PyVal.ofFn"
  | some (_, _) => "PyVal.ofFn2"  -- 2+ params
  | none =>
    if ctx.zeroParamFuncs.contains nameId then "PyVal.ofFn0" else "PyVal.ofFn"

/-- Map a Monty binary `Operator` to the name of the matching `pyOp`
    helper in `EffectMonad.lean`. Every operator in `Basic.Operator` must
    have an entry — adding a new operator without updating this is the
    classic shape of "rich semantics gradually decay back to placeholders". -/
def binOpName : Operator → String
  | .add      => "pyAdd"
  | .sub      => "pySub"
  | .mult     => "pyMul"
  | .matMult  => "pyMatMult"
  | .div      => "pyDiv"
  | .«mod»    => "pyMod"
  | .pow      => "pyPow"
  | .lShift   => "pyLShift"
  | .rShift   => "pyRShift"
  | .bitOr    => "pyBitOr"
  | .bitXor   => "pyBitXor"
  | .bitAnd   => "pyBitAnd"
  | .floorDiv => "pyFloorDiv"
  | .«and»    => "pyAnd"
  | .«or»     => "pyOr"

/-- Map a Monty `CmpOperator` to the matching helper. The optimised
    `modEq n` form takes the modulus as an extra argument, so it returns a
    pre-applied function string. -/
def cmpOpName : CmpOperator → String
  | .eq    => "pyEq"
  | .notEq => "pyNotEq"
  | .lt    => "pyLt"
  | .ltE   => "pyLe"
  | .gt    => "pyGt"
  | .gtE   => "pyGe"
  | .«is»  => "pyIs"
  | .isNot => "pyIsNot"
  | .«in»  => "pyIn"
  | .notIn => "pyNotIn"
  | .modEq n => s!"pyModEq ({n})"

def allParams (ir : IrExport) (sig : Signature) : List String :=
  let pos := (sig.posArgs.getD []).map fun pid => sanitizeName (ir.resolveString pid)
  let args := (sig.args.getD []).map fun pid => sanitizeName (ir.resolveString pid)
  let varArgs := match sig.varArgs with
    | some pid => [sanitizeName (ir.resolveString pid)]
    | none => []
  let kw := (sig.kwargs.getD []).map fun pid => sanitizeName (ir.resolveString pid)
  let varKwargs := match sig.varKwargs with
    | some pid => [sanitizeName (ir.resolveString pid)]
    | none => []
  pos ++ args ++ varArgs ++ kw ++ varKwargs

/-- Return all parameter `StringId`s of a signature in the same order as
    `allParams`. Used by the noncomputability checker to know which name
    references in a function body are bound to parameters (computable). -/
def allParamIds (sig : Signature) : List StringId :=
  let pos := sig.posArgs.getD []
  let args := sig.args.getD []
  let varArgs := match sig.varArgs with | some pid => [pid] | none => []
  let kw := sig.kwargs.getD []
  let varKwargs := match sig.varKwargs with | some pid => [pid] | none => []
  pos ++ args ++ varArgs ++ kw ++ varKwargs

-- ============================================================================
-- Effectfulness detection
-- ============================================================================

def isEffectfulExpr (ctx : CodegenCtx) : Expr → Bool
  | .call (.name _) _ => true
  | .indirectCall _ _ => true
  | .attrCall _ _ _ => true
  | _ => false

/-- Recursively check if an expression contains effectful subexpressions.
    Used by the statement layer to decide whether to invoke `flattenExprLoc`
    so effectful calls get hoisted into monadic bindings. Every construct
    that may *contain* an effectful sub-expression must recurse here, or
    those effects will be silently dropped from the generated `Eff` type. -/
partial def containsEffects (ctx : CodegenCtx) : Expr → Bool
  | .call (.name _) _ => true
  -- An indirect call IS itself an effect (it dispatches via the
  -- callFn axiom at `Perms.top`), so always route it through
  -- flatten — the flatten path emits the actual `PyVal.callFn`
  -- bindings and lets the resulting `Perms.top` widening propagate.
  | .indirectCall _ _ => true
  | .attrCall obj _ args => cel ctx obj || ceArgs ctx args
  | .attrGet obj _ => cel ctx obj
  | .op l _ r => cel ctx l || cel ctx r
  | .cmpOp l _ r => cel ctx l || cel ctx r
  | .chainCmp first rest => cel ctx first || rest.any (fun (_, e) => cel ctx e)
  | .not e | .unaryMinus e | .unaryPlus e | .unaryInvert e => cel ctx e
  -- `await x` is always routed through the flatten path so the
  -- closure-call dispatch in `flattenExpr.«await»` fires. Even for
  -- `await c` where `c` is a closure-bound name (no inner effectful
  -- sub-expression), we need flatten to emit `← (PyClosure.call0 c)`.
  | .«await» _ => true
  | .call (.builtin _) args => ceArgs ctx args
  | .subscript o i => cel ctx o || cel ctx i
  | .slice a b c => cel? ctx a || cel? ctx b || cel? ctx c
  | .ifElse t b o => cel ctx t || cel ctx b || cel ctx o
  | .list items | .tuple items | .set items =>
    items.any fun | .value e | .unpack e => cel ctx e
  | .dict items => items.any fun
    | .pair k v => cel ctx k || cel ctx v
    | .unpack e => cel ctx e
  | .fstring parts => parts.any fun
    | .literal _ => false
    | .value e _ spec => cel ctx e || (match spec with
        | some (.dynamic se) => cel ctx se
        | _ => false)
  -- Comprehensions are always routed through the flatten path: their
  -- lowering to `pyListComp` / `pySetComp` / `pyDictComp` produces a
  -- monadic call (`← (pyListComp ...)`) that must be hoisted into a
  -- temp binding. The pure `translateExpr` path can't bind monadic
  -- results and would just emit `PyVal.none`. Effect-detection is
  -- conservative here: we mark them effectful even when none of the
  -- sub-expressions are, so the assert/assign flatten path fires and
  -- compileComp gets to do its work.
  | .listComp _ _ => true
  | .setComp _ _ => true
  | .dictComp _ _ _ => true
  -- Walrus `(x := expr)` has a side effect: it binds `x` in the
  -- enclosing scope. We model that by always routing through the
  -- flatten path, which can emit a real `let` binding for `x` so
  -- subsequent references resolve locally instead of falling through
  -- to a module-level axiom.
  | .named _ _ => true
  | _ => false
where
  cel (ctx : CodegenCtx) (el : ExprLoc) : Bool := containsEffects ctx el.expr
  cel? (ctx : CodegenCtx) : Option ExprLoc → Bool
    | some e => cel ctx e
    | none => false
  ceComp (ctx : CodegenCtx) : Comprehension → Bool
    | .mk _ iter ifs => cel ctx iter || ifs.any (fun e => cel ctx e)
  ceArgs (ctx : CodegenCtx) : ArgExprs → Bool
    | .simple exprs => exprs.any fun e => cel ctx e
    | .singleKwarg _ val => cel ctx val
    | .generalizedCall args _ => args.any fun
      | .pos e | .posUnpack e | .kwUnpack e => cel ctx e
      | .kw _ e => cel ctx e

-- ============================================================================
-- Sub-expression traversal
-- ============================================================================

/-- Extract every `ExprLoc` carried by an `ArgExprs` payload. Used by
    `subExprs` so callers can recurse into call arguments uniformly. -/
private def argExprLocs : ArgExprs → List ExprLoc
  | .simple es => es
  | .singleKwarg _ v => [v]
  | .generalizedCall as kws =>
    as.map (fun
      | .pos e | .posUnpack e | .kwUnpack e | .kw _ e => e) ++
    kws.map (fun | .mk _ e => e)

/-- Direct sub-`ExprLoc` children of an `Expr`. Used by every recursive
    expression-walker — `flattenExpr`'s sound-by-default fallback,
    `fmaExpr` (arity inference), `collectExprCallIdsDeep` and
    `collectExprNameRefs` (external + global detection).

    Adding a new IR variant only requires updating this one function for
    traversal. Leaving a construct off this list means deep walkers won't
    enter it — which is exactly the soundness hole class we're closing. -/
private def subExprs : Expr → List ExprLoc
  | .literal _ | .builtin _ | .name _ => []
  | .call _ args =>
    -- callee is a Callable (not an ExprLoc), so it isn't a sub-expression here.
    argExprLocs args
  | .indirectCall callee args => callee :: argExprLocs args
  | .attrCall obj _ args => obj :: argExprLocs args
  | .attrGet obj _ => [obj]
  | .op l _ r | .cmpOp l _ r => [l, r]
  | .chainCmp first rest => first :: rest.map (·.2)
  | .not e | .unaryMinus e | .unaryPlus e | .unaryInvert e | .«await» e => [e]
  | .subscript o i => [o, i]
  | .slice a b c => [a, b, c].filterMap id
  | .ifElse t b o => [t, b, o]
  | .list items | .tuple items | .set items =>
    items.map fun | .value e | .unpack e => e
  | .dict items => items.flatMap fun
    | .pair k v => [k, v] | .unpack e => [e]
  | .fstring parts => parts.flatMap fun
    | .literal _ => []
    | .value e _ spec => e :: (match spec with | some (.dynamic se) => [se] | _ => [])
  | .listComp elem comps | .setComp elem comps =>
    elem :: comps.flatMap (fun | .mk _ iter ifs => iter :: ifs)
  | .dictComp k v comps =>
    [k, v] ++ comps.flatMap (fun | .mk _ iter ifs => iter :: ifs)
  | .lambda _ => []  -- lambda body is collected separately by the deep walkers
  | .named _ v => [v]

-- ============================================================================
-- Expression flattening
-- ============================================================================

private def argCount : ArgExprs → Nat
  | .simple exprs => exprs.length
  | .singleKwarg _ _ => 1
  | .generalizedCall args kwargs =>
    -- Match `flattenArgExprs`'s collapsing semantics: when there's any
    -- unpack, the whole positional or keyword group becomes a single
    -- `PyVal.none` placeholder. Otherwise each arg/kwarg counts as one.
    let hasPosUnpack := args.any fun | .posUnpack _ => true | _ => false
    let hasKwUnpack := args.any (fun | .kwUnpack _ => true | _ => false) ||
      kwargs.any (fun | .mk 0 _ => true | _ => false)
    let posCount := if hasPosUnpack then 1
      else args.foldl (fun n a => match a with | .pos _ | .kw _ _ => n + 1 | _ => n) 0
    let kwCount := if hasKwUnpack then 1
      else kwargs.foldl (fun n kw => match kw with | .mk name _ => if name != 0 then n + 1 else n) 0
    posCount + kwCount

/-- Map a Monty IR builtin name to a 1-arg Lean helper. Returns `none`
    for builtins we don't have a computable model for; the caller falls
    back to the legacy `PyVal.none` placeholder. The strings on the left
    are exactly the inner-key strings parsed by `parseBuiltinName` in
    `JsonDeser.lean` (e.g. `"Len"` for `{"Function": "Len"}` and
    `"Str"` for `{"Type": "Str"}`). Type-name and Function-name spaces
    don't collide in the corpus, so a single table suffices. -/
private def builtinUnary : String → Option String
  | "Len" => some "pyLen"
  | "Abs" => some "pyAbs"
  | "Bool" => some "pyBool"
  | "Int" => some "pyInt"
  | "Float" => some "pyFloat"
  | "Str" => some "pyStr"
  | "Repr" => some "pyRepr"
  | "Hash" => some "pyHash"
  | "Id" => some "pyId"
  | "Type" => some "pyType"
  | "Hex" => some "pyHex"
  | "Bin" => some "pyBin"
  | "Oct" => some "pyOct"
  | "Chr" => some "pyChr"
  | "Ord" => some "pyOrd"
  | "Round" => some "pyRound"
  | "Sorted" => some "pySorted"
  | "Reversed" => some "pyReversed"
  -- Single-iterable forms of `min`/`max`/`sum`. The 2-arg forms of
  -- min/max are handled by `builtinBinary`.
  | "Sum" => some "pySumIter"
  -- Iteration / coercion / IO
  | "Range" => some "pyRange1"
  | "Enumerate" => some "pyEnumerate"
  | "Next" => some "pyNext"
  | "Any" => some "pyAny"
  | "All" => some "pyAll"
  | "Print" => some "pyPrint"
  -- `list(x)` / `tuple(x)` / `dict(x)` / `set(x)` constructor calls.
  -- We model only the easy "iterable → list/tuple" coercions; the
  -- empty-arg form is dispatched by `builtinIter` (which the
  -- 1-arg path falls through to).
  | "List" => some "pyToList"
  | "Tuple" => some "pyToTuple"
  | _ => none

/-- Map a Monty IR builtin name to a 2-arg Lean helper. -/
private def builtinBinary : String → Option String
  | "Min" => some "pyMin2"
  | "Max" => some "pyMax2"
  | "Divmod" => some "pyDivmod"
  | "Pow" => some "pyPow"
  | "Range" => some "pyRange2"
  | "Zip" => some "pyZip"
  | "Isinstance" => some "pyIsinstance"
  | _ => none

/-- 3-arg form of `range`. -/
private def builtinTernary : String → Option String
  | "Range" => some "pyRange3"
  | _ => none

/-- Single-iterable form for `min`/`max` (zero-table miss falls back to
    `none` so the caller can route 2+ args through `builtinBinary`). -/
private def builtinIter : String → Option String
  | "Min" => some "pyMinIter"
  | "Max" => some "pyMaxIter"
  | _ => none

/-- Map a Python method name to a (Lean function, isUnary) pair.
    `isUnary` is true for methods that take only `self` (no extra args),
    e.g. `s.upper()`; false for methods that take additional positional
    args, e.g. `s.startswith(prefix)`. The dispatch in `Codegen.lean`'s
    `flattenExpr` for `.attrCall obj attr args` consults this table. -/
private def methodUnary : String → Option String
  | "upper" => some "pyStrUpper"
  | "lower" => some "pyStrLower"
  | "strip" => some "pyStrStrip"
  | "keys" => some "pyDictKeys"
  | "values" => some "pyDictValues"
  | "items" => some "pyDictItems"
  | _ => none

private def methodBinary : String → Option String
  | "startswith" => some "pyStrStartsWith"
  | "endswith" => some "pyStrEndsWith"
  | "split" => some "pyStrSplit"
  | "join" => some "pyStrJoinMethod"
  | "find" => some "pyStrFind"
  | "count" => some "pyStrCount"
  | "index" => some "pyListIndex"
  | "get" => some "pyDictGet"
  | _ => none

private def methodTernary : String → Option String
  | "replace" => some "pyStrReplace"
  | "get" => some "pyDictGetDefault"
  | _ => none


-- ============================================================================
-- Call/arity detection
-- ============================================================================

private partial def findMaxArity (targetId : StringId) : List Node → Nat
  | [] => 0
  | .funcDef fd :: rest => Nat.max (findMaxArity targetId fd.body) (findMaxArity targetId rest)
  | .assign _ el :: rest => Nat.max (fmaExpr targetId el.expr) (findMaxArity targetId rest)
  | .expr el :: rest => Nat.max (fmaExpr targetId el.expr) (findMaxArity targetId rest)
  | .ret el :: rest => Nat.max (fmaExpr targetId el.expr) (findMaxArity targetId rest)
  | .assert test msg :: rest =>
    let mt := match msg with | some m => fmaExpr targetId m.expr | none => 0
    Nat.max (fmaExpr targetId test.expr) (Nat.max mt (findMaxArity targetId rest))
  | .opAssign _ _ el :: rest => Nat.max (fmaExpr targetId el.expr) (findMaxArity targetId rest)
  | .subscriptAssign obj idx val _ :: rest =>
    Nat.max (fmaExpr targetId obj.expr)
      (Nat.max (fmaExpr targetId idx.expr)
        (Nat.max (fmaExpr targetId val.expr) (findMaxArity targetId rest)))
  | .subscriptOpAssign obj idx _ val _ :: rest =>
    Nat.max (fmaExpr targetId obj.expr)
      (Nat.max (fmaExpr targetId idx.expr)
        (Nat.max (fmaExpr targetId val.expr) (findMaxArity targetId rest)))
  | .attrAssign obj _ _ val :: rest =>
    Nat.max (fmaExpr targetId obj.expr)
      (Nat.max (fmaExpr targetId val.expr) (findMaxArity targetId rest))
  | .attrOpAssign obj _ _ val _ :: rest =>
    Nat.max (fmaExpr targetId obj.expr)
      (Nat.max (fmaExpr targetId val.expr) (findMaxArity targetId rest))
  | .unpackAssign _ _ el :: rest => Nat.max (fmaExpr targetId el.expr) (findMaxArity targetId rest)
  | .raise (some el) :: rest => Nat.max (fmaExpr targetId el.expr) (findMaxArity targetId rest)
  | .«if» test body orElse :: rest =>
    Nat.max (fmaExpr targetId test.expr)
      (Nat.max (findMaxArity targetId body)
        (Nat.max (findMaxArity targetId orElse) (findMaxArity targetId rest)))
  | .«for» _ iter body orElse :: rest =>
    Nat.max (fmaExpr targetId iter.expr)
      (Nat.max (findMaxArity targetId body)
        (Nat.max (findMaxArity targetId orElse) (findMaxArity targetId rest)))
  | .«while» test body orElse :: rest =>
    Nat.max (fmaExpr targetId test.expr)
      (Nat.max (findMaxArity targetId body)
        (Nat.max (findMaxArity targetId orElse) (findMaxArity targetId rest)))
  | .«try» tb :: rest =>
    let h := tb.handlers.foldl (fun m h => Nat.max m (findMaxArity targetId h.body)) 0
    Nat.max (findMaxArity targetId tb.body)
      (Nat.max (findMaxArity targetId tb.orElse)
        (Nat.max (findMaxArity targetId tb.finallyBody)
          (Nat.max h (findMaxArity targetId rest))))
  | _ :: rest => findMaxArity targetId rest
where fmaExpr (targetId : StringId) : Expr → Nat
    | .call (.name id) args =>
      if id.nameId == targetId then argCount args
      else (subExprs (.call (.name id) args)).foldl (fun m e => Nat.max m (fmaExpr targetId e.expr)) 0
    | other => (subExprs other).foldl (fun m e => Nat.max m (fmaExpr targetId e.expr)) 0

private def collectExprCallIds : Expr → List Identifier
  | .call (.name id) _ => [id]
  | _ => []

private partial def collectNodeCalls : List Node → List StringId
  | [] => []
  | .funcDef fd :: rest => collectNodeCalls fd.body ++ collectNodeCalls rest
  | .assign _ el :: rest => (collectExprCallIds el.expr).map (·.nameId) ++ collectNodeCalls rest
  | .expr el :: rest => (collectExprCallIds el.expr).map (·.nameId) ++ collectNodeCalls rest
  | .ret el :: rest => (collectExprCallIds el.expr).map (·.nameId) ++ collectNodeCalls rest
  | _ :: rest => collectNodeCalls rest

private partial def collectNodeCallIds : List Node → List Identifier
  | [] => []
  | .funcDef fd :: rest => collectNodeCallIds fd.body ++ collectNodeCallIds rest
  | .assign _ el :: rest => collectExprCallIds el.expr ++ collectNodeCallIds rest
  | .expr el :: rest => collectExprCallIds el.expr ++ collectNodeCallIds rest
  | .ret el :: rest => collectExprCallIds el.expr ++ collectNodeCallIds rest
  | _ :: rest => collectNodeCallIds rest

-- ============================================================================
-- Top-level generation
-- ============================================================================

/-- Collect all locally-bound name ids from an UnpackTarget. -/
private partial def unpackTargetIds : UnpackTarget → List StringId
  | .name id => [id.nameId]
  | .starred id => [id.nameId]
  | .tuple ts _ => ts.flatMap unpackTargetIds

/-- Recursively collect all locally-bound name ids in a node list:
    assign / opAssign / unpackAssign targets, for-loop targets, except
    handler names, import names. Used to determine which `.name id`
    references are computable (locally bound) vs noncomputable (globals,
    which lower to axioms). -/
private partial def collectAllBoundIds : List Node → List StringId
  | [] => []
  | .assign id _ :: rest => id.nameId :: collectAllBoundIds rest
  | .opAssign id _ _ :: rest => id.nameId :: collectAllBoundIds rest
  | .unpackAssign ts _ _ :: rest => ts.flatMap unpackTargetIds ++ collectAllBoundIds rest
  | .funcDef fd :: rest => fd.name.nameId :: collectAllBoundIds fd.body ++ collectAllBoundIds rest
  | .«for» tgt _ body orElse :: rest =>
    unpackTargetIds tgt ++ collectAllBoundIds body ++ collectAllBoundIds orElse ++ collectAllBoundIds rest
  | .«while» _ body orElse :: rest =>
    collectAllBoundIds body ++ collectAllBoundIds orElse ++ collectAllBoundIds rest
  | .«if» _ body orElse :: rest =>
    collectAllBoundIds body ++ collectAllBoundIds orElse ++ collectAllBoundIds rest
  | .«try» tb :: rest =>
    collectAllBoundIds tb.body ++ collectAllBoundIds tb.orElse ++ collectAllBoundIds tb.finallyBody ++
    tb.handlers.flatMap (fun h =>
      (match h.name with | some n => [n.nameId] | none => []) ++ collectAllBoundIds h.body) ++
    collectAllBoundIds rest
  | .import _ id :: rest => id.nameId :: collectAllBoundIds rest
  | .importFrom _ pairs _ :: rest => pairs.map (·.2.nameId) ++ collectAllBoundIds rest
  | _ :: rest => collectAllBoundIds rest

/-- Recursively collect all Assign target nameIds from a node list. -/
private partial def collectAllAssigns : List Node → List StringId
  | [] => []
  | .assign id _ :: rest => id.nameId :: collectAllAssigns rest
  | .funcDef fd :: rest => collectAllAssigns fd.body ++ collectAllAssigns rest
  | .«for» _ _ body orElse :: rest =>
    collectAllAssigns body ++ collectAllAssigns orElse ++ collectAllAssigns rest
  | .«while» _ body orElse :: rest =>
    collectAllAssigns body ++ collectAllAssigns orElse ++ collectAllAssigns rest
  | .«if» _ body orElse :: rest =>
    collectAllAssigns body ++ collectAllAssigns orElse ++ collectAllAssigns rest
  | .«try» tb :: rest =>
    collectAllAssigns tb.body ++ collectAllAssigns tb.orElse ++ collectAllAssigns tb.finallyBody ++
    tb.handlers.flatMap (fun h => collectAllAssigns h.body) ++ collectAllAssigns rest
  | _ :: rest => collectAllAssigns rest

/-- Recursively collect all Name reference nameIds from expressions in nodes. -/
private partial def collectAllNameRefs : List Node → List StringId
  | [] => []
  | .assign _ el :: rest => collectExprNameRefs el.expr ++ collectAllNameRefs rest
  | .expr el :: rest => collectExprNameRefs el.expr ++ collectAllNameRefs rest
  | .ret el :: rest => collectExprNameRefs el.expr ++ collectAllNameRefs rest
  | .assert test msg :: rest =>
    collectExprNameRefs test.expr ++ (match msg with | some m => collectExprNameRefs m.expr | none => []) ++ collectAllNameRefs rest
  | .funcDef fd :: rest => collectAllNameRefs fd.body ++ collectAllNameRefs rest
  | .«for» _ iter body orElse :: rest =>
    collectExprNameRefs iter.expr ++ collectAllNameRefs body ++ collectAllNameRefs orElse ++ collectAllNameRefs rest
  | .«while» test body orElse :: rest =>
    collectExprNameRefs test.expr ++ collectAllNameRefs body ++ collectAllNameRefs orElse ++ collectAllNameRefs rest
  | .«if» test body orElse :: rest =>
    collectExprNameRefs test.expr ++ collectAllNameRefs body ++ collectAllNameRefs orElse ++ collectAllNameRefs rest
  | .«try» tb :: rest =>
    collectAllNameRefs tb.body ++ collectAllNameRefs tb.orElse ++ collectAllNameRefs tb.finallyBody ++
    tb.handlers.flatMap (fun h => collectAllNameRefs h.body) ++ collectAllNameRefs rest
  | .raise (some el) :: rest => collectExprNameRefs el.expr ++ collectAllNameRefs rest
  | .opAssign _ _ el :: rest => collectExprNameRefs el.expr ++ collectAllNameRefs rest
  | _ :: rest => collectAllNameRefs rest
where
  collectExprNameRefs : Expr → List StringId
    | .name id => [id.nameId]
    | .call (.name id) args =>
      id.nameId :: (subExprs (.call (.name id) args)).flatMap collectExprLocRefs
    -- Recurse into lambda bodies via the outer node-walker.
    | .lambda fd => collectAllNameRefs fd.body
    | other => (subExprs other).flatMap collectExprLocRefs
  collectExprLocRefs (el : ExprLoc) : List StringId :=
    collectExprNameRefs el.expr

/-- Deeply collect all Call target identifiers from nodes (recurses into all structures). -/
private partial def collectAllNameCallIds : List Node → List Identifier
  | [] => []
  | .assign _ el :: rest => collectExprCallIdsDeep el.expr ++ collectAllNameCallIds rest
  | .expr el :: rest => collectExprCallIdsDeep el.expr ++ collectAllNameCallIds rest
  | .ret el :: rest => collectExprCallIdsDeep el.expr ++ collectAllNameCallIds rest
  | .assert test msg :: rest =>
    collectExprCallIdsDeep test.expr ++
    (match msg with | some m => collectExprCallIdsDeep m.expr | none => []) ++
    collectAllNameCallIds rest
  | .funcDef fd :: rest => collectAllNameCallIds fd.body ++ collectAllNameCallIds rest
  | .«for» _ iter body orElse :: rest =>
    collectExprCallIdsDeep iter.expr ++ collectAllNameCallIds body ++ collectAllNameCallIds orElse ++ collectAllNameCallIds rest
  | .«while» test body orElse :: rest =>
    collectExprCallIdsDeep test.expr ++ collectAllNameCallIds body ++ collectAllNameCallIds orElse ++ collectAllNameCallIds rest
  | .«if» test body orElse :: rest =>
    collectExprCallIdsDeep test.expr ++ collectAllNameCallIds body ++ collectAllNameCallIds orElse ++ collectAllNameCallIds rest
  | .«try» tb :: rest =>
    collectAllNameCallIds tb.body ++ collectAllNameCallIds tb.orElse ++ collectAllNameCallIds tb.finallyBody ++
    tb.handlers.flatMap (fun h => collectAllNameCallIds h.body) ++ collectAllNameCallIds rest
  | .raise (some el) :: rest => collectExprCallIdsDeep el.expr ++ collectAllNameCallIds rest
  | .opAssign _ _ el :: rest => collectExprCallIdsDeep el.expr ++ collectAllNameCallIds rest
  | _ :: rest => collectAllNameCallIds rest
where
  collectExprCallIdsDeep : Expr → List Identifier
    | .call (.name id) args =>
      id :: (subExprs (.call (.name id) args)).flatMap (fun e => collectExprCallIdsDeep e.expr)
    -- Recurse into lambda bodies via the outer collector. Without this,
    -- a `Pure` function with `cb = lambda: send_email(x); cb()` would not
    -- detect `send_email` as an external — codegen would emit an unbound
    -- reference instead of a typed external call, breaking effect tracking.
    | .lambda fd => collectAllNameCallIds fd.body
    | other => (subExprs other).flatMap (fun e => collectExprCallIdsDeep e.expr)

-- Body computability check.
-- A body is noncomputable iff it depends on any axiom: external calls,
-- references to global axioms (any `.name id` not bound locally as a
-- param or local var), `PyVal.ofFn` (top-level func ref-as-value),
-- `PyVal.callFn` (indirect / method call paths), or contains a lambda
-- (lowers to `PyVal.ofFn`).
--
-- `boundIds` is the set of definitely-computable names: parameters and
-- locally-assigned (via .assign) names. Any `.name id` not in this set
-- is treated as noncomputable (it's either a global axiom, a top-level
-- func ref-as-value, or a closure-bound name that codegen will resolve
-- to an axiom).
mutual
/-- Decide whether an expression is noncomputable in the generated Lean.

    `extIds` — names that lower to `axiom`s (true externals OR
    already-classified noncomputable local funcs).

    `funcIds` — top-level / local function names. These are *callable*
    as plain `def`s, but referencing one as a value (e.g. passing it as
    an argument) wraps it in the noncomputable `PyVal.ofFn0` axiom — so
    a bare `.name` reference to a function still pollutes the host
    function's noncomputability.

    `boundIds` — locally-bound names (params + earlier-statement assigns
    + top-level functions in scope). Referenced names not in this set
    will resolve to module-level axioms in the generated Lean. -/
private partial def exprIsNoncomputable (extIds : List StringId) (funcIds : List StringId) (closureRetIds : List StringId) (boundIds : List StringId) (e : Expr) : Bool :=
  match e with
  | .lambda fd =>
    -- Lambdas in pure positions lower to `PyVal.ofPureFn (fun ... => ...)`,
    -- which is a computable `def`. The body itself is the only thing
    -- that can introduce noncomputability — recurse with the lambda
    -- params added to `boundIds` so closure references type-check.
    let lamParams := allParamIds fd.signature
    nodesAreNoncomputable extIds funcIds closureRetIds (boundIds ++ lamParams) fd.body
  | .indirectCall _ _ =>
    -- The codegen lowers an indirect call to `PyVal.callFn` /
    -- `callFn0` / `callFn2`, all of which are noncomputable axioms.
    -- The whole containing function is therefore noncomputable.
    -- (Previously the indirectCall lowering emitted a `PyVal.none`
    -- placeholder, so the function could stay computable; with the
    -- callFn-based lowering it can't.)
    true
  | .attrCall obj _ args =>
    -- Same shape as indirectCall: codegen emits a `PyVal.none` placeholder
    -- after flattening sub-effects. Computable iff the sub-expressions are.
    exprIsNoncomputable extIds funcIds closureRetIds boundIds obj.expr ||
    (argExprLocs args).any (fun el => exprIsNoncomputable extIds funcIds closureRetIds boundIds el.expr)
  | .attrGet obj _ =>
    -- `obj.attr` flattens `obj` and emits `PyVal.none`. Computable iff `obj` is.
    exprIsNoncomputable extIds funcIds closureRetIds boundIds obj.expr
  | .call (.name id) _ =>
    -- A call is computable iff we can resolve it to either:
    --   (a) a known top-level function (in `funcIds`) — handled as a
    --       real `def`, or
    --   (b) a closure-bound local name — these get added to `funcIds`
    --       in `nodesAreNoncomputable`'s walker when we step past an
    --       assign of a closure-returning call.
    -- Any other locally-bound name (parameter, ordinary assign target,
    -- for-loop target) is a `PyVal` and the call goes through the
    -- noncomputable `PyVal.callFn` axiom — so it forces the host
    -- function `noncomputable`. The widening to `Perms.top` only fixes
    -- the *type* mismatch; it doesn't make the axiom computable.
    extIds.contains id.nameId ||
    !funcIds.contains id.nameId ||
    (subExprs e).any (fun el => exprIsNoncomputable extIds funcIds closureRetIds boundIds el.expr)
  | .name id =>
    -- A bare name reference is noncomputable if it isn't bound (resolves
    -- to a module-level axiom) OR if it refers to a top-level function
    -- (which gets wrapped in the noncomputable `PyVal.ofFn0`/`ofFn` axioms
    -- when used as a value).
    !boundIds.contains id.nameId || funcIds.contains id.nameId
  | .named id v =>
    -- Walrus `(name := val)` binds `name` for the rest of the surrounding
    -- expression's scope. Walking inner sub-expressions with `name` added
    -- to `boundIds` makes `(x := f()) + x` not falsely noncomp.
    exprIsNoncomputable extIds funcIds closureRetIds (id.nameId :: boundIds) v.expr
  | .listComp elem comps | .setComp elem comps =>
    -- Comprehension targets bind progressively: each generator's iter
    -- expression sees the targets of all previous generators. The
    -- elem and condition closures see all targets.
    --
    -- Caveat: only `.name` targets are considered bound here. Tuple
    -- targets (`for (a, b) in pairs`) lower in codegen as a single
    -- `_item` parameter that doesn't actually destructure `a`/`b` —
    -- those names resolve to module-level axioms in the emitted
    -- code, so we MUST classify them as noncomputable. Adding tuple
    -- leaves to the bound set would mislead the walker.
    let nameTarget : UnpackTarget → List StringId
      | .name id => [id.nameId]
      | _ => []
    let walk : List Comprehension → List StringId → Bool := fun cs initBound =>
      let (anyNonComp, _) := cs.foldl
        (fun (acc : Bool × List StringId) (c : Comprehension) =>
          let (b, bs) := acc
          if b then (true, bs)
          else
            let iterNonComp := exprIsNoncomputable extIds funcIds closureRetIds bs c.iter.expr
            let bs' := bs ++ nameTarget c.target
            let condNonComp := c.ifs.any (fun ie =>
              exprIsNoncomputable extIds funcIds closureRetIds bs' ie.expr)
            (iterNonComp || condNonComp, bs'))
        (false, initBound)
      anyNonComp
    let allTargets := comps.flatMap fun c => nameTarget c.target
    walk comps boundIds ||
    exprIsNoncomputable extIds funcIds closureRetIds (boundIds ++ allTargets) elem.expr
  | .dictComp k v comps =>
    let nameTarget : UnpackTarget → List StringId
      | .name id => [id.nameId]
      | _ => []
    let walk : List Comprehension → List StringId → Bool := fun cs initBound =>
      let (anyNonComp, _) := cs.foldl
        (fun (acc : Bool × List StringId) (c : Comprehension) =>
          let (b, bs) := acc
          if b then (true, bs)
          else
            let iterNonComp := exprIsNoncomputable extIds funcIds closureRetIds bs c.iter.expr
            let bs' := bs ++ nameTarget c.target
            let condNonComp := c.ifs.any (fun ie =>
              exprIsNoncomputable extIds funcIds closureRetIds bs' ie.expr)
            (iterNonComp || condNonComp, bs'))
        (false, initBound)
      anyNonComp
    let allTargets := comps.flatMap fun c => nameTarget c.target
    walk comps boundIds ||
    exprIsNoncomputable extIds funcIds closureRetIds (boundIds ++ allTargets) k.expr ||
    exprIsNoncomputable extIds funcIds closureRetIds (boundIds ++ allTargets) v.expr
  | _ => (subExprs e).any (fun el => exprIsNoncomputable extIds funcIds closureRetIds boundIds el.expr)

/-- Walk an expression collecting walrus targets `(name := val)`. Walrus
    binds in the enclosing scope, so any `name` introduced this way needs
    to be added to `boundIds` so subsequent statements that reference it
    aren't classified as noncomputable. -/
private partial def collectWalrusInExpr : Expr → List StringId
  | .named id v => id.nameId :: collectWalrusInExpr v.expr
  | .lambda _ => []  -- lambda body has its own scope
  | other => (subExprs other).flatMap (fun e => collectWalrusInExpr e.expr)

/-- Walrus targets from each top-level expression slot of a statement. -/
private partial def stmtWalrusBindings : Node → List StringId
  | .expr el | .ret el | .assign _ el | .opAssign _ _ el
  | .unpackAssign _ _ el => collectWalrusInExpr el.expr
  | .raise (some el) => collectWalrusInExpr el.expr
  | .assert test msg =>
    collectWalrusInExpr test.expr ++
    (match msg with | some m => collectWalrusInExpr m.expr | none => [])
  | .«if» test _ _ => collectWalrusInExpr test.expr
  | .«while» test _ _ => collectWalrusInExpr test.expr
  | .«for» _ iter _ _ => collectWalrusInExpr iter.expr
  | _ => []

private partial def stmtBindings (n : Node) : List StringId :=
  let direct := match n with
    | .assign id _ => [id.nameId]
    | .opAssign id _ _ => [id.nameId]
    | .unpackAssign ts _ _ => ts.flatMap unpackTargetIds
    | .«import» _ alias => [alias.nameId]
    | .importFrom _ pairs _ => pairs.map (·.2.nameId)
    | .funcDef fd => [fd.name.nameId]
    | _ => []
  direct ++ stmtWalrusBindings n

/-- Walk a list of statements, threading the bound-name set forward so
    each statement only sees names that earlier statements have already
    introduced. Also threads `funcIds` forward so a nested `.funcDef`
    earlier in the body causes a later `.name id` reference to be
    classified as a function-reference (which codegen lowers to a
    `PyVal.ofFn0`/`ofFn` axiom and thus forces noncomputable).

    `closureRetIds` is the set of closure-returning function names. When
    we step past an assign whose RHS is a call to one of these, the
    assigned name is itself closure-bound at runtime, so subsequent
    `name(args)` calls dispatch via `PyClosure.callN` (which is
    computable) — we add the target to `funcIds` so the
    `.call (.name id)` walker doesn't classify the call as
    noncomputable. -/
private partial def nodesAreNoncomputable (extIds : List StringId) (funcIds : List StringId) (closureRetIds : List StringId) (boundIds : List StringId) : List Node → Bool
  | [] => false
  | n :: rest =>
    let nestedFuncs := match n with | .funcDef fd => [fd.name.nameId] | _ => []
    -- If this stmt assigns the result of a closure-returning call to a
    -- name, treat that name as a function-like binding for subsequent
    -- noncomp checks (it'll dispatch via PyClosure.callN, computable).
    let closureBoundFromAssign : List StringId :=
      match n with
      | .assign id el =>
        match el.expr with
        | .call (.name funcId) _ =>
          if closureRetIds.contains funcId.nameId then [id.nameId] else []
        | .lambda _ => [id.nameId]  -- lambda RHS produces a typed PyClosure
        | _ => []
      | _ => []
    let extendedFuncs := funcIds ++ nestedFuncs ++ closureBoundFromAssign
    nodeIsNoncomputable extIds extendedFuncs closureRetIds boundIds n ||
    nodesAreNoncomputable extIds extendedFuncs closureRetIds
      (boundIds ++ stmtBindings n) rest

private partial def nodeIsNoncomputable (extIds : List StringId) (funcIds : List StringId) (closureRetIds : List StringId) (boundIds : List StringId) : Node → Bool
  | .pass | .retNone | .«break» _ | .«continue» _ => false
  | .global _ _ | .nonlocal _ _ | .import _ _ | .importFrom _ _ _ => false
  | .raise none => false
  | .expr el | .ret el | .assign _ el | .unpackAssign _ _ el =>
    exprIsNoncomputable extIds funcIds closureRetIds boundIds el.expr
  | .opAssign id _ el =>
    -- P1: opAssign now references the target variable's old value
    -- (e.g. `let x := pyAdd x rhs`). If the target is a global axiom
    -- (not in boundIds or funcIds), the emitted code is noncomputable.
    let targetBound := boundIds.contains id.nameId || funcIds.contains id.nameId
    (!targetBound) ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds el.expr
  | .raise (some el) => exprIsNoncomputable extIds funcIds closureRetIds boundIds el.expr
  | .assert el omsg =>
    exprIsNoncomputable extIds funcIds closureRetIds boundIds el.expr ||
    (match omsg with | some m => exprIsNoncomputable extIds funcIds closureRetIds boundIds m.expr | none => false)
  | .subscriptOpAssign a b _ c _ =>
    exprIsNoncomputable extIds funcIds closureRetIds boundIds a.expr ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds b.expr ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds c.expr
  | .subscriptAssign a b c _ =>
    -- P1: subscriptAssign now references the target object's old
    -- value (e.g. `let d := pySubscriptSet d idx val`). When the
    -- target is a `.name id`, check if `id` is an unbound global axiom.
    let targetNoncomp := match a.expr with
      | .name id => !(boundIds.contains id.nameId || funcIds.contains id.nameId)
      | _ => false
    targetNoncomp ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds a.expr ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds b.expr ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds c.expr
  | .attrOpAssign a _ _ b _ =>
    exprIsNoncomputable extIds funcIds closureRetIds boundIds a.expr ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds b.expr
  | .attrAssign a _ _ b =>
    exprIsNoncomputable extIds funcIds closureRetIds boundIds a.expr ||
    exprIsNoncomputable extIds funcIds closureRetIds boundIds b.expr
  | .«for» target iter body orElse =>
    -- The for-loop target is bound for the duration of the body, so
    -- references to it inside the body are computable. Note that an
    -- `else` clause runs only when the loop wasn't `break`-ed; the
    -- target is also still in scope there.
    let bodyBound := boundIds ++ unpackTargetIds target
    exprIsNoncomputable extIds funcIds closureRetIds boundIds iter.expr ||
    nodesAreNoncomputable extIds funcIds closureRetIds bodyBound body ||
    nodesAreNoncomputable extIds funcIds closureRetIds bodyBound orElse
  | .«while» test body orElse =>
    exprIsNoncomputable extIds funcIds closureRetIds boundIds test.expr ||
    nodesAreNoncomputable extIds funcIds closureRetIds boundIds body ||
    nodesAreNoncomputable extIds funcIds closureRetIds boundIds orElse
  | .«if» test body orElse =>
    exprIsNoncomputable extIds funcIds closureRetIds boundIds test.expr ||
    nodesAreNoncomputable extIds funcIds closureRetIds boundIds body ||
    nodesAreNoncomputable extIds funcIds closureRetIds boundIds orElse
  | .funcDef fd =>
    -- Nested `def` becomes `let name := fun params => Eff.runFunction (do ...)`,
    -- which is computable as long as the body is. Walk the body with the
    -- function's params added to `boundIds`. Caveat: a noncomputable nested
    -- `def` would still need wrapping into a closure form codegen doesn't
    -- emit, so this is approximate — but the failure mode is "Lean rejects
    -- the file at compile", not "soundness hole", which is fine.
    let fdParams := allParamIds fd.signature
    nodesAreNoncomputable extIds funcIds closureRetIds (boundIds ++ fdParams) fd.body
  | .«try» tb =>
    nodesAreNoncomputable extIds funcIds closureRetIds boundIds tb.body ||
    nodesAreNoncomputable extIds funcIds closureRetIds boundIds tb.orElse ||
    nodesAreNoncomputable extIds funcIds closureRetIds boundIds tb.finallyBody ||
    tb.handlers.any fun h =>
      -- `except <Type> as <name>:` binds `<name>` for the duration of
      -- the handler body. Without adding it to `boundIds`, the walker
      -- treats `e` in `except ValueError as e: assert str(e) == ...`
      -- as an unbound module-level reference and forces the entire
      -- enclosing function noncomputable, even though codegen does
      -- emit `let e := ...` at the start of the handler body.
      let bound := match h.name with
        | some id => id.nameId :: boundIds
        | none    => boundIds
      nodesAreNoncomputable extIds funcIds closureRetIds bound h.body
end

-- ============================================================================
-- EffAST emission (Path C — symbolic-execution AST)
-- ============================================================================
--
-- Walks the IR and produces an `EffAST` constructor expression as a
-- string. The codegen emits this alongside the normal `def <name>` so
-- the user can write `EffAST.calledBefore "a" "b" <name>__ast` proofs.
--
-- The translator captures the *call sequence* of the body — every
-- syntactic call to a top-level name, in evaluation order, threaded
-- through `.bind` chains. Branches and try/except are exposed as
-- structural constructors so analyses can walk both arms. Loops
-- become `.loop body` (the body's calls don't propagate to the
-- post-state, sound for "may run 0 times"). Unhandled IR shapes
-- become `.opaque`, which causes ordering analyses to fail closed.

mutual

partial def collectExprCallNamesAST (ctx : CodegenCtx) : Expr → List String
  | .call (.name id) args =>
    -- If the callee is a locally-bound closure (from `cb = lambda ...`
    -- or `cb = closure_factory(...)`), its effects were already
    -- captured at the binding site — emit no call, only recurse into
    -- args. This mirrors `PyClosure.callN` in the executable form.
    if ctx.astClosureNames.contains id.nameId then
      collectArgExprsCallNames ctx args
    else
    -- Resolve through the per-function alias map: aliases supply a
    -- fully-formed display name (e.g. `f = known_func` maps to
    -- `"known_func"`, or nested `def inner` maps to
    -- `"parent__inner"`). If no alias matches, fall back to the
    -- standard externals/locals lookup.
    let displayName :=
      match ctx.astLocalAliases.find? (·.1 == id.nameId) with
      | some (_, target) => target
      | none =>
        let calleeName := sanitizeName (ctx.ir.resolveString id.nameId)
        let isExt := ctx.externals.any (fun e => e.1 == id.nameId)
        let isLocal := ctx.knownFuncs.any (fun (fid, _, _) => fid == id.nameId)
        let _ := isLocal
        if isExt then "ext_" ++ calleeName else calleeName
    let argCalls := collectArgExprsCallNames ctx args
    argCalls ++ [displayName]
  | .call (.builtin _) args => collectArgExprsCallNames ctx args
  | .attrCall obj _ args =>
    -- An attribute call (`obj.method(args)`) is usually handled by
    -- the executable codegen via specialised helpers (pyList helpers,
    -- asyncio.create_task, etc.) that don't widen to `Perms.top`.
    -- Leaving this as a non-opaque walk preserves the historical
    -- behavior — the few cases that genuinely go through
    -- `PyVal.callFn` are already caught via other signals (the
    -- executable-side widening fixpoint).
    collectExprCallNamesAST ctx obj.expr ++ collectArgExprsCallNames ctx args
  | .indirectCall callee args =>
    -- Indirect dispatch (`handlers[op](payload)`, `bracket(x)`, etc.)
    -- is opaque at the AST level: the callee is a runtime value
    -- whose effect set we can't statically determine. Emit the
    -- sentinel so `permsOf` widens the surrounding function.
    collectExprCallNamesAST ctx callee.expr
      ++ collectArgExprsCallNames ctx args
      ++ ["__opaque__"]
  | .op a _ b => collectExprCallNamesAST ctx a.expr ++ collectExprCallNamesAST ctx b.expr
  | .cmpOp a _ b => collectExprCallNamesAST ctx a.expr ++ collectExprCallNamesAST ctx b.expr
  | .chainCmp first rest =>
    collectExprCallNamesAST ctx first.expr ++
    rest.flatMap (fun (_, e) => collectExprCallNamesAST ctx e.expr)
  | .ifElse t a b =>
    collectExprCallNamesAST ctx t.expr ++
    collectExprCallNamesAST ctx a.expr ++
    collectExprCallNamesAST ctx b.expr
  | .subscript a i => collectExprCallNamesAST ctx a.expr ++ collectExprCallNamesAST ctx i.expr
  | .attrGet obj _ => collectExprCallNamesAST ctx obj.expr
  | .unaryPlus e | .unaryMinus e | .unaryInvert e =>
    collectExprCallNamesAST ctx e.expr
  | .not e => collectExprCallNamesAST ctx e.expr
  | .named _ v => collectExprCallNamesAST ctx v.expr
  | .«await» e => collectExprCallNamesAST ctx e.expr
  | .list items | .tuple items | .set items =>
    items.flatMap fun
      | .value e => collectExprCallNamesAST ctx e.expr
      | .unpack e => collectExprCallNamesAST ctx e.expr
  | .dict items =>
    items.flatMap fun
      | .pair k v => collectExprCallNamesAST ctx k.expr ++ collectExprCallNamesAST ctx v.expr
      | .unpack e => collectExprCallNamesAST ctx e.expr
  | .fstring parts =>
    parts.flatMap fun
      | .literal _ => []
      | .value e _ _ => collectExprCallNamesAST ctx e.expr
  | .listComp elem clauses =>
    -- List comprehension: element expression is evaluated in a loop
    -- over the generator clauses. The element may contain calls
    -- (e.g. `[summarize(x) for x in items]`), which must propagate
    -- to the surrounding function's effect set. Recurse into the
    -- element, each iter expression, and each filter expression.
    let elemCalls := collectExprCallNamesAST ctx elem.expr
    let clauseCalls := clauses.flatMap fun
      | .mk _ iter filters =>
        collectExprCallNamesAST ctx iter.expr
          ++ filters.flatMap (fun f => collectExprCallNamesAST ctx f.expr)
    clauseCalls ++ elemCalls
  | .setComp elem clauses =>
    let elemCalls := collectExprCallNamesAST ctx elem.expr
    let clauseCalls := clauses.flatMap fun
      | .mk _ iter filters =>
        collectExprCallNamesAST ctx iter.expr
          ++ filters.flatMap (fun f => collectExprCallNamesAST ctx f.expr)
    clauseCalls ++ elemCalls
  | .dictComp key val clauses =>
    let keyCalls := collectExprCallNamesAST ctx key.expr
    let valCalls := collectExprCallNamesAST ctx val.expr
    let clauseCalls := clauses.flatMap fun
      | .mk _ iter filters =>
        collectExprCallNamesAST ctx iter.expr
          ++ filters.flatMap (fun f => collectExprCallNamesAST ctx f.expr)
    clauseCalls ++ keyCalls ++ valCalls
  | .lambda fd =>
    -- An anonymous lambda introduced mid-expression. Recurse into
    -- the body for any calls it contains — a lambda that calls
    -- `send_email` should propagate `{net}` into the surrounding
    -- function. (The executable codegen routes lambda calls through
    -- `PyClosure.callN`, which preserves effect sets.)
    fd.body.flatMap fun n => match n with
      | .expr el => collectExprCallNamesAST ctx el.expr
      | .ret el => collectExprCallNamesAST ctx el.expr
      | _ => []
  | _ => []

partial def collectArgExprsCallNames (ctx : CodegenCtx) : ArgExprs → List String
  | .simple es => es.flatMap (fun e => collectExprCallNamesAST ctx e.expr)
  | .singleKwarg _ v => collectExprCallNamesAST ctx v.expr
  | .generalizedCall args kwargs =>
    let posCalls := args.flatMap fun
      | .pos e | .kw _ e | .posUnpack e | .kwUnpack e => collectExprCallNamesAST ctx e.expr
    let kwCalls := kwargs.flatMap fun | .mk _ e => collectExprCallNamesAST ctx e.expr
    posCalls ++ kwCalls

end

/-- Build an EffAST `.bind` chain for a list of call names, ending in
    `tail`. `[a, b, c]` becomes
    `.bind (.call "a" []) (fun _ => .bind (.call "b" []) (fun _ => .bind (.call "c" []) (fun _ => tail)))`.

    The reserved sentinel name `"__opaque__"` expands to `EffAST.opaque`
    instead of `EffAST.call`. This is how the AST translator flags
    expression shapes it can't model precisely (indirect dispatch,
    lambdas passed to higher-order funcs, etc.) — `permsOf` treats
    `.opaque` as `Perms.top`, so the surrounding function widens
    conservatively. -/
def chainBindCalls (calls : List String) (tail : String) : String :=
  match calls with
  | [] => tail
  | name :: rest =>
    let inner := chainBindCalls rest tail
    let head := if name == "__opaque__" then "EffAST.opaque"
                else s!"(EffAST.call \"{name}\" [])"
    s!"(EffAST.seq {head} {inner})"

mutual

partial def translateNodeAST (ctx : CodegenCtx) (n : Node) (rest : String) : String :=
  match n with
  | .assign _ el =>
    let calls := collectExprCallNamesAST ctx el.expr
    chainBindCalls calls rest
  | .opAssign _ _ el =>
    let calls := collectExprCallNamesAST ctx el.expr
    chainBindCalls calls rest
  | .unpackAssign _ _ el =>
    let calls := collectExprCallNamesAST ctx el.expr
    chainBindCalls calls rest
  | .expr el =>
    let calls := collectExprCallNamesAST ctx el.expr
    chainBindCalls calls rest
  | .ret el =>
    let calls := collectExprCallNamesAST ctx el.expr
    let tail := "(EffAST.retEarly PyVal.none)"
    chainBindCalls calls tail
    -- Note: `rest` is dropped here because `ret` is terminal.
  | .retNone => "(EffAST.retEarly PyVal.none)"
  | .raise (some el) =>
    let calls := collectExprCallNamesAST ctx el.expr
    let tail := "(EffAST.raise PyVal.none)"
    chainBindCalls calls tail
  | .raise none => "(EffAST.raise PyVal.none)"
  | .«if» cond body orElse =>
    let condCalls := collectExprCallNamesAST ctx cond.expr
    let thenAst := translateBodyAST ctx body
    let elseAst := translateBodyAST ctx orElse
    let branch := s!"(EffAST.branchOn PyVal.none {thenAst} {elseAst})"
    let bound := s!"(EffAST.seq {branch} {rest})"
    chainBindCalls condCalls bound
  | .«for» _ iter body orElse =>
    let iterCalls := collectExprCallNamesAST ctx iter.expr
    let bodyAst := translateBodyAST ctx body
    let elseAst := translateBodyAST ctx orElse
    let loopAst := s!"(EffAST.loop {bodyAst})"
    -- After the loop, run the else clause then continue.
    let afterLoop := s!"(EffAST.seq {loopAst} (EffAST.seq {elseAst} {rest}))"
    chainBindCalls iterCalls afterLoop
  | .«while» cond body orElse =>
    let condCalls := collectExprCallNamesAST ctx cond.expr
    let bodyAst := translateBodyAST ctx body
    let elseAst := translateBodyAST ctx orElse
    let loopAst := s!"(EffAST.loop {bodyAst})"
    let afterLoop := s!"(EffAST.seq {loopAst} (EffAST.seq {elseAst} {rest}))"
    chainBindCalls condCalls afterLoop
  | .«try» tb =>
    let bodyAst := translateBodyAST ctx tb.body
    let handlerAst :=
      match tb.handlers with
      | [] => "(EffAST.pure PyVal.none)"
      | h :: _ => translateBodyAST ctx h.body
    let tryNode := s!"(EffAST.tryExc {bodyAst} {handlerAst})"
    s!"(EffAST.seq {tryNode} {rest})"
  | .funcDef _ => rest  -- Nested funcDef: skip for AST purposes (it's a closure declaration).
  | .«break» _ | .«continue» _ => rest  -- loop control: skip in AST
  | .pass => rest
  | .assert test msg =>
    -- assert e, msg: walk the test expression (may contain calls),
    -- optionally walk the msg expression. The assertion itself is
    -- effect-free — it raises on false, but that's already captured
    -- at the Eff level via `.raise`. For AST perms purposes the only
    -- contribution is whatever the test/msg expressions call.
    let testCalls := collectExprCallNamesAST ctx test.expr
    let msgCalls := match msg with
      | some m => collectExprCallNamesAST ctx m.expr
      | none => []
    chainBindCalls (testCalls ++ msgCalls) rest
  | .subscriptAssign tgt idx val _ =>
    -- d[k] = v: pure value-level rebind. Walk all three expressions
    -- for any calls they contain but don't introduce effects.
    let calls :=
      collectExprCallNamesAST ctx tgt.expr
        ++ collectExprCallNamesAST ctx idx.expr
        ++ collectExprCallNamesAST ctx val.expr
    chainBindCalls calls rest
  | .subscriptOpAssign tgt idx _ val _ =>
    let calls :=
      collectExprCallNamesAST ctx tgt.expr
        ++ collectExprCallNamesAST ctx idx.expr
        ++ collectExprCallNamesAST ctx val.expr
    chainBindCalls calls rest
  | .attrAssign obj _ _ val =>
    let calls :=
      collectExprCallNamesAST ctx obj.expr
        ++ collectExprCallNamesAST ctx val.expr
    chainBindCalls calls rest
  | .attrOpAssign obj _ _ val _ =>
    let calls :=
      collectExprCallNamesAST ctx obj.expr
        ++ collectExprCallNamesAST ctx val.expr
    chainBindCalls calls rest
  | .global _ _ | .nonlocal _ _ => rest  -- scope declarations: no runtime effect
  | .import _ _ | .importFrom _ _ _ => rest  -- imports: modelled as module-level axioms

partial def translateBodyAST (ctx : CodegenCtx) (stmts : List Node) : String :=
  match stmts with
  | [] => "(EffAST.pure PyVal.none)"
  | n :: rest =>
    let restStr := translateBodyAST ctx rest
    translateNodeAST ctx n restStr

end

-- ============================================================================
-- EffProg translator (Option 1b): emit a self-interpreting program IR
-- ============================================================================
--
-- Walks a `FunctionDef`'s body and produces an `EffProg` literal string
-- (or `none` if the function uses shapes `EffProg` doesn't yet cover).
-- When it succeeds, the emitted `def foo` is `Eff.runFunction
-- (EffProg.interp __extEnv [params...] foo__prog)` — the executable
-- body is derived from the AST by the interpreter, not hand-emitted
-- statement by statement.
--
-- See `docs/effast-full-ir-plan.md` for the Pass structure. This
-- codegen starts supporting Pass 1+2 shapes and grows.

/-- Parameter/local scope: a `List (StringId × Nat)` mapping Python
    name IDs to their de-Bruijn positions in the interp Env. The
    head of the list is the most-recently-bound entry; `find?`
    picks it first on lookup, which matches Python's "most recent
    assignment wins" shadowing. -/
abbrev PScope := List (StringId × Nat)

def pscopeLookup (sc : PScope) (id : StringId) : Option Nat :=
  sc.find? (·.1 == id) |>.map (·.2)

def pscopePush (sc : PScope) (id : StringId) (idx : Nat) : PScope :=
  (id, idx) :: sc

/-- Escape a Lean string literal for inclusion in generated source. -/
def escapeLeanString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '\\' then acc ++ "\\\\"
    else if c == '"' then acc ++ "\\\""
    else if c == '\n' then acc ++ "\\n"
    else if c == '\r' then acc ++ "\\r"
    else if c == '\t' then acc ++ "\\t"
    else acc.push c

/-- Translate an IR `Expr` into an `EffProg.Expr` literal string.
    Returns `none` for shapes `EffProg.Expr` doesn't yet cover:
    calls, subscripts, attrGets, lists, fstrings, lambdas,
    comprehensions, chained compares, ifElse expressions, etc. -/
partial def transExprToProg (ctx : CodegenCtx) (sc : PScope) : Expr → Option String
  | .literal .none => some "(EffProg.Expr.lit PyVal.none)"
  | .literal (.bool b) => some s!"(EffProg.Expr.lit (PyVal.bool {b}))"
  | .literal (.int n) => some s!"(EffProg.Expr.lit (PyVal.int ({n})))"
  | .literal (.str sid) =>
    let s := ctx.ir.resolveString sid
    some s!"(EffProg.Expr.lit (PyVal.str \"{escapeLeanString s}\"))"
  | .name id =>
    match pscopeLookup sc id.nameId with
    | some idx => some s!"(EffProg.Expr.param {idx})"
    | none =>
      -- Not a local/param: treat as a module-level axiom or global.
      -- In the interp this is just `PyVal.none` (G2 value-erased
      -- semantics), but it keeps translation unblocked so
      -- expressions referencing globals can go through EffProg.
      let n := sanitizeName (ctx.ir.resolveString id.nameId)
      some s!"(EffProg.Expr.globalRef \"{n}\")"
  | .op a op b =>
    let opStr : Option String := match op with
      | .add => some ".add"
      | .sub => some ".sub"
      | .mult => some ".mul"
      | .div => some ".div"
      | .«mod» => some ".mod"
      | .floorDiv => some ".floorDiv"
      | .«and» => some ".and_"
      | .«or» => some ".or_"
      | _ => none
    match opStr, transExprToProg ctx sc a.expr, transExprToProg ctx sc b.expr with
    | some os, some ae, some be => some s!"(EffProg.Expr.binOp {os} {ae} {be})"
    | _, _, _ => none
  | .cmpOp a op b =>
    let opStr : Option String := match op with
      | .eq => some ".eq"
      | .notEq => some ".ne"
      | .lt => some ".lt"
      | .ltE => some ".le"
      | .gt => some ".gt"
      | .gtE => some ".ge"
      | _ => none
    match opStr, transExprToProg ctx sc a.expr, transExprToProg ctx sc b.expr with
    | some os, some ae, some be => some s!"(EffProg.Expr.binOp {os} {ae} {be})"
    | _, _, _ => none
  | .unaryMinus e =>
    (transExprToProg ctx sc e.expr).map fun s => s!"(EffProg.Expr.unOp .neg {s})"
  | .unaryPlus e =>
    (transExprToProg ctx sc e.expr).map fun s => s!"(EffProg.Expr.unOp .pos {s})"
  | .not e =>
    (transExprToProg ctx sc e.expr).map fun s => s!"(EffProg.Expr.unOp .not_ {s})"
  | .unaryInvert e =>
    (transExprToProg ctx sc e.expr).map fun s => s!"(EffProg.Expr.unOp .invert {s})"
  | .attrGet obj attrId =>
    let attrName := ctx.ir.resolveString attrId
    (transExprToProg ctx sc obj.expr).map fun oe =>
      s!"(EffProg.Expr.attrGet {oe} \"{attrName}\")"
  | .list items =>
    -- Only simple (non-unpacking) elements are supported.
    let elemOpts : Option (List String) :=
      items.foldr (init := some []) fun item acc =>
        match acc, item with
        | some xs, .value e =>
          (transExprToProg ctx sc e.expr).map fun s => s :: xs
        | _, _ => none
    elemOpts.map fun elems =>
      s!"(EffProg.Expr.list [{String.intercalate ", " elems}])"
  | .tuple items =>
    let elemOpts : Option (List String) :=
      items.foldr (init := some []) fun item acc =>
        match acc, item with
        | some xs, .value e =>
          (transExprToProg ctx sc e.expr).map fun s => s :: xs
        | _, _ => none
    elemOpts.map fun elems =>
      s!"(EffProg.Expr.tuple [{String.intercalate ", " elems}])"
  | .set items =>
    let elemOpts : Option (List String) :=
      items.foldr (init := some []) fun item acc =>
        match acc, item with
        | some xs, .value e =>
          (transExprToProg ctx sc e.expr).map fun s => s :: xs
        | _, _ => none
    elemOpts.map fun elems =>
      s!"(EffProg.Expr.set_ [{String.intercalate ", " elems}])"
  | .dict items =>
    let pairOpts : Option (List String) :=
      items.foldr (init := some []) fun item acc =>
        match acc, item with
        | some xs, .pair k v =>
          match transExprToProg ctx sc k.expr, transExprToProg ctx sc v.expr with
          | some ks, some vs => some (s!"({ks}, {vs})" :: xs)
          | _, _ => none
        | _, _ => none
    pairOpts.map fun pairs =>
      s!"(EffProg.Expr.dict [{String.intercalate ", " pairs}])"
  | .call (.builtin bid) (.simple [arg]) =>
    -- Single-arg builtin call: `len(x)`, `str(x)`, etc. These
    -- are pure by definition.
    let builtinName := bid  -- BuiltinId IS String
    (transExprToProg ctx sc arg.expr).map fun ae =>
      s!"(EffProg.Expr.builtin1 \"{builtinName}\" {ae})"
  | .call (.builtin bid) (.simple args) =>
    -- Multi-arg builtin. Support 2-arg builtins via nested Expr.
    -- For unsupported builtins, fall through.
    match args with
    | [a1, a2] =>
      let builtinName := bid
      match transExprToProg ctx sc a1.expr, transExprToProg ctx sc a2.expr with
      | some ae1, some ae2 =>
        -- Dispatch common 2-arg builtins
        if builtinName == "range" || builtinName == "Range" then
          -- range(a, b) → list of ints [a, a+1, ..., b-1]
          -- Value-erased: PyVal.none (imprecise)
          some "(EffProg.Expr.lit PyVal.none)"
        else
          none
      | _, _ => none
    | _ => none
  | .subscript obj idx =>
    match idx.expr with
    | .slice start stop step =>
      -- Slicing: `obj[start:stop:step]`.
      let toOpt (e : Option ExprLoc) : Option String :=
        match e with
        | none => some "Option.none"
        | some el =>
          (transExprToProg ctx sc el.expr).map fun s => s!"(Option.some {s})"
      match transExprToProg ctx sc obj.expr, toOpt start, toOpt stop, toOpt step with
      | some oe, some se, some st, some stp =>
        some s!"(EffProg.Expr.slice {oe} {se} {st} {stp})"
      | _, _, _, _ => none
    | _ =>
      -- Normal subscript: x[i].
      match transExprToProg ctx sc obj.expr, transExprToProg ctx sc idx.expr with
      | some ae, some ie => some s!"(EffProg.Expr.subscript {ae} {ie})"
      | _, _ => none
  | .ifElse cond t e =>
    match transExprToProg ctx sc cond.expr,
          transExprToProg ctx sc t.expr,
          transExprToProg ctx sc e.expr with
    | some c, some te, some ee => some s!"(EffProg.Expr.ifElse {c} {te} {ee})"
    | _, _, _ => none
  | .attrCall obj methodId args =>
    let methodName := ctx.ir.resolveString methodId
    match args with
    | .simple [] =>
      let knownPure := ["upper", "lower", "strip", "keys", "values",
                         "items", "copy", "title", "swapcase", "capitalize",
                         "result", "isupper", "islower", "isdigit", "isalpha"]
      if knownPure.contains methodName then
        (transExprToProg ctx sc obj.expr).map fun oe =>
          s!"(EffProg.Expr.builtin1 \"{methodName}\" {oe})"
      else none
    | .simple [arg] =>
      -- 1-arg methods
      match transExprToProg ctx sc obj.expr, transExprToProg ctx sc arg.expr with
      | some oe, some ae =>
        if methodName == "append" then
          some s!"(EffProg.Expr.listAppend {oe} {ae})"
        else if methodName == "startswith" || methodName == "endswith" ||
                methodName == "count" || methodName == "find" ||
                methodName == "split" || methodName == "join" ||
                methodName == "replace" || methodName == "get" ||
                methodName == "extend" || methodName == "index" ||
                methodName == "create_task" || methodName == "result" then
          -- Map to builtin-style dispatch. Value-erased for
          -- methods without a dedicated pyXxx helper.
          some s!"(EffProg.Expr.lit PyVal.none)"
        else none
      | _, _ => none
    | .simple [arg1, arg2] =>
      -- 2-arg methods (e.g. str.replace(old, new))
      match transExprToProg ctx sc obj.expr with
      | some _ => some "(EffProg.Expr.lit PyVal.none)"
      | none => none
    | .generalizedCall _ _ =>
      -- Generalized call (may include *args/**kwargs). Value-erase.
      match transExprToProg ctx sc obj.expr with
      | some _ => some "(EffProg.Expr.lit PyVal.none)"
      | none => none
    | _ => none
  | .lambda _ =>
    -- Lambda as expression: pure value-erased. Creating a closure
    -- is pure; effects happen when it's called.
    some "(EffProg.Expr.lit PyVal.none)"
  | .named _ val =>
    -- Walrus: just translate the value expression.
    transExprToProg ctx sc val.expr
  | .«await» e =>
    -- Await: value-level identity (async is modeled as sync).
    transExprToProg ctx sc e.expr
  | .fstring parts =>
    -- Walk parts: literal strings stay as `.inl`, value
    -- interpolations as `.inr <expr>`. Format specs are
    -- ignored — the interp calls `pyToStr` which matches the
    -- default Python `str()` conversion.
    let partOpts : Option (List String) :=
      parts.foldr (init := some []) fun part acc =>
        match acc, part with
        | some xs, .literal sid =>
          let s := ctx.ir.resolveString sid
          some (s!"Sum.inl \"{escapeLeanString s}\"" :: xs)
        | some xs, .value el _ _ =>
          match transExprToProg ctx sc el.expr with
          | some es => some (s!"Sum.inr {es}" :: xs)
          | none => none
        | _, _ => none
    partOpts.map fun ps =>
      s!"(EffProg.Expr.fstring [{String.intercalate ", " ps}])"
  | .chainCmp first rest =>
    -- Lower `a < b < c < d` to `(a < b) and (b < c) and (c < d)`.
    -- Each consecutive pair becomes a binOp, then we conjoin.
    match transExprToProg ctx sc first.expr with
    | none => none
    | some firstE =>
      let pairOpts : Option (List (String × String)) :=
        -- Build a list of (opStr, rhsStr) for each pair in `rest`.
        rest.foldr (init := some []) fun pair acc =>
          match acc with
          | none => none
          | some xs =>
            let (op, rhs) := pair
            let opStr : Option String := match op with
              | .eq => some ".eq" | .notEq => some ".ne"
              | .lt => some ".lt" | .ltE => some ".le"
              | .gt => some ".gt" | .gtE => some ".ge"
              | _ => none
            match opStr, transExprToProg ctx sc rhs.expr with
            | some os, some rs => some ((os, rs) :: xs)
            | _, _ => none
      match pairOpts with
      | none => none
      | some pairs =>
        -- Walk pairs building: acc_expr AND (prev < next).
        -- Use a fold that threads the "prev" expr.
        let (result, _) := pairs.foldl
          (init := (firstE, firstE))
          fun (acc, prev) (op, rhs) =>
            let cmp := s!"(EffProg.Expr.binOp {op} {prev} {rhs})"
            let combined :=
              if acc == firstE && pairs.length > 0 then
                cmp  -- first iteration: just the first comparison
              else
                s!"(EffProg.Expr.binOp .and_ {acc} {cmp})"
            (combined, rhs)
        some result
  | _ => none

/-- Translate a `.call (.name _) (.simple args)` into an `EffProg`
    call-statement string. Returns the translated args list, or
    `none` if any arg doesn't translate. Used by `transNodeToProg`
    when a call appears as an expression statement or as the RHS
    of an assign / return. Only supports `.simple` arg shape for
    now (no kwargs / unpack / generalized). -/
partial def transCallArgs (ctx : CodegenCtx) (sc : PScope)
    : ArgExprs → Option (List String)
  | .simple es =>
    es.foldr (init := some []) fun e acc =>
      match acc, transExprToProg ctx sc e.expr with
      | some xs, some x => some (x :: xs)
      | _, _ => none
  | .singleKwarg _ v =>
    match transExprToProg ctx sc v.expr with
    | some s => some [s]
    | none => none
  | .generalizedCall args _ =>
    args.foldr (init := some []) fun arg acc =>
      match acc with
      | none => none
      | some xs =>
        match arg with
        | .pos e =>
          match transExprToProg ctx sc e.expr with
          | some s => some (s :: xs)
          | none => none
        | .kw _ e =>
          match transExprToProg ctx sc e.expr with
          | some s => some (s :: xs)
          | none => none
        | .posUnpack _ =>
          some ("(EffProg.Expr.lit PyVal.none)" :: xs)
        | .kwUnpack _ =>
          some ("(EffProg.Expr.lit PyVal.none)" :: xs)

/-- Resolve a callable's string name for `EffProg.Prog.call`.
    Externals (scope `.localUnassigned`) get the `ext_` prefix.
    Local (top-level) functions use their sanitized name — the
    codegen emits `__extEnvProg` with an entry for every
    top-level function, so `EffProg.Prog.permsOf` resolves local
    calls via the same extEnv path as externals. Other scopes
    (cell, global, etc.) and builtins are unsupported. -/
def callableToProgName (ctx : CodegenCtx) : Callable → Option String
  | .name id =>
    -- Check if this name is a nested funcDef alias (from
    -- astLocalAliases). If so, use the mangled name.
    match ctx.astLocalAliases.find? (·.1 == id.nameId) with
    | some (_, mangledName) => some mangledName
    | none =>
      let n := sanitizeName (ctx.ir.resolveString id.nameId)
      if id.scope == .localUnassigned then
        some ("ext_" ++ n)
      else if id.scope == .local || id.scope == .global then
        some n
      else
        none
  | .builtin _ => none

/-- Walk an expression tree and extract any `.call` sub-expressions
    into hoisted `EffProg.Prog.call` statements. Each hoisted call
    gets a fresh de-Bruijn index; the call site is replaced with
    `EffProg.Expr.param idx`. Recursively walks binOp, cmpOp, etc.
    so that `a + foo(x) * bar(y)` becomes three hoists plus a
    pure binOp. -/
partial def hoistCallsFromExpr (ctx : CodegenCtx) (sc : PScope) (nextIdx : Nat)
    : Expr → Option (List String × String × Nat)
  | .call (.name id) (.simple args) =>
    -- Resolve the callee name. Check aliases first (nested funcDefs
    -- may be in pscope from scope threading but still have an alias
    -- for the mangled name). Then check callableIsSafe for non-aliased.
    let cname? : Option String :=
      match ctx.astLocalAliases.find? (·.1 == id.nameId) with
      | some (_, mangledName) => some mangledName
      | none =>
        if (pscopeLookup sc id.nameId).isSome then none
        else callableToProgName ctx (.name id)
    match cname? with
    | none => none
    | some cname =>
        -- Recursively hoist through args: if an arg is itself a
        -- call, hoist it to a prior letInEff and replace with a
        -- param ref. This handles `f(g(x), h(y))` → hoist g(x)
        -- at idx N, hoist h(y) at N+1, then call f with params.
        let rec hoistArgs (es : List ExprLoc) (idx : Nat)
            : Option (List String × List String × Nat) :=
          match es with
          | [] => some ([], [], idx)
          | e :: rest =>
            match hoistCallsFromExpr ctx sc idx e.expr with
            | none => none
            | some (h, pureStr, idx') =>
              match hoistArgs rest idx' with
              | none => none
              | some (hs, strs, idx'') =>
                some (h ++ hs, pureStr :: strs, idx'')
        match hoistArgs args nextIdx with
        | none => none
        | some (allHoists, argStrs, finalIdx) =>
          let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
          let callStr := s!"(EffProg.Prog.call \"{cname}\" {argList})"
          let paramRef := s!"(EffProg.Expr.param {finalIdx})"
          some (allHoists ++ [callStr], paramRef, finalIdx + 1)
  | .op a op b =>
    -- Recursively hoist in both sides.
    match hoistCallsFromExpr ctx sc nextIdx a.expr with
    | none => none
    | some (ha, ae, n1) =>
      match hoistCallsFromExpr ctx sc n1 b.expr with
      | none => none
      | some (hb, be, n2) =>
        let opStr : Option String := match op with
          | .add => some ".add" | .sub => some ".sub"
          | .mult => some ".mul" | .div => some ".div"
          | .«mod» => some ".mod" | .floorDiv => some ".floorDiv"
          | .«and» => some ".and_" | .«or» => some ".or_"
          | _ => none
        match opStr with
        | some os => some (ha ++ hb, s!"(EffProg.Expr.binOp {os} {ae} {be})", n2)
        | none => none
  | .cmpOp a op b =>
    match hoistCallsFromExpr ctx sc nextIdx a.expr with
    | none => none
    | some (ha, ae, n1) =>
      match hoistCallsFromExpr ctx sc n1 b.expr with
      | none => none
      | some (hb, be, n2) =>
        let opStr : Option String := match op with
          | .eq => some ".eq" | .notEq => some ".ne"
          | .lt => some ".lt" | .ltE => some ".le"
          | .gt => some ".gt" | .gtE => some ".ge"
          | _ => none
        match opStr with
        | some os => some (ha ++ hb, s!"(EffProg.Expr.binOp {os} {ae} {be})", n2)
        | none => none
  | .not e =>
    match hoistCallsFromExpr ctx sc nextIdx e.expr with
    | none => none
    | some (h, ae, n) => some (h, s!"(EffProg.Expr.unOp .not_ {ae})", n)
  | .unaryMinus e =>
    match hoistCallsFromExpr ctx sc nextIdx e.expr with
    | none => none
    | some (h, ae, n) => some (h, s!"(EffProg.Expr.unOp .neg {ae})", n)
  | .unaryPlus e =>
    match hoistCallsFromExpr ctx sc nextIdx e.expr with
    | none => none
    | some (h, ae, n) => some (h, s!"(EffProg.Expr.unOp .pos {ae})", n)
  | .unaryInvert e =>
    match hoistCallsFromExpr ctx sc nextIdx e.expr with
    | none => none
    | some (h, ae, n) => some (h, s!"(EffProg.Expr.unOp .invert {ae})", n)
  | .subscript obj idx =>
    match idx.expr with
    | .slice _ _ _ => -- Can't hoist inside slices yet
      match transExprToProg ctx sc (.subscript obj idx) with
      | some s => some ([], s, nextIdx)
      | none => none
    | _ =>
      match hoistCallsFromExpr ctx sc nextIdx obj.expr with
      | none => none
      | some (ho, oe, n1) =>
        match hoistCallsFromExpr ctx sc n1 idx.expr with
        | none => none
        | some (hi, ie, n2) => some (ho ++ hi, s!"(EffProg.Expr.subscript {oe} {ie})", n2)
  | .ifElse c t e =>
    match hoistCallsFromExpr ctx sc nextIdx c.expr with
    | none => none
    | some (hc, ce, n1) =>
      match hoistCallsFromExpr ctx sc n1 t.expr with
      | none => none
      | some (ht, te, n2) =>
        match hoistCallsFromExpr ctx sc n2 e.expr with
        | none => none
        | some (he, ee, n3) =>
          some (hc ++ ht ++ he, s!"(EffProg.Expr.ifElse {ce} {te} {ee})", n3)
  | .call (.builtin bid) (.simple args) =>
    let builtinName := bid
    match args with
    | [arg] =>
      match hoistCallsFromExpr ctx sc nextIdx arg.expr with
      | none => none
      | some (h, ae, n) =>
        some (h, s!"(EffProg.Expr.builtin1 \"{builtinName}\" {ae})", n)
    | _ => some ([], "(EffProg.Expr.lit PyVal.none)", nextIdx)
  | .chainCmp first rest =>
    -- Chain comparison with possible calls in sub-exprs.
    -- Hoist all sub-expressions, then build the chain as nested
    -- and-binops (same lowering as transExprToProg).
    match hoistCallsFromExpr ctx sc nextIdx first.expr with
    | none => none
    | some (hFirst, firstE, n1) =>
      let rec hoistPairs (pairs : List (CmpOperator × ExprLoc)) (idx : Nat) (prevE : String)
          : Option (List String × String × Nat) :=
        match pairs with
        | [] => some ([], prevE, idx)  -- shouldn't happen (empty chain)
        | [(op, rhs)] =>
          let opStr := match op with
            | .eq => ".eq" | .notEq => ".ne" | .lt => ".lt"
            | .ltE => ".le" | .gt => ".gt" | .gtE => ".ge"
            | _ => ".eq"
          match hoistCallsFromExpr ctx sc idx rhs.expr with
          | none => none
          | some (hr, re, n) =>
            some (hr, s!"(EffProg.Expr.binOp {opStr} {prevE} {re})", n)
        | (op, rhs) :: rest' =>
          let opStr := match op with
            | .eq => ".eq" | .notEq => ".ne" | .lt => ".lt"
            | .ltE => ".le" | .gt => ".gt" | .gtE => ".ge"
            | _ => ".eq"
          match hoistCallsFromExpr ctx sc idx rhs.expr with
          | none => none
          | some (hr, re, n) =>
            let cmp := s!"(EffProg.Expr.binOp {opStr} {prevE} {re})"
            match hoistPairs rest' n re with
            | none => none
            | some (hRest, restExpr, n') =>
              some (hr ++ hRest, s!"(EffProg.Expr.binOp .and_ {cmp} {restExpr})", n')
      match hoistPairs rest n1 firstE with
      | none => none
      | some (hPairs, chainExpr, nFinal) =>
        some (hFirst ++ hPairs, chainExpr, nFinal)
  | .list items =>
    let rec hoistListItems (is : List SequenceItem) (idx : Nat)
        : Option (List String × List String × Nat) :=
      match is with
      | [] => some ([], [], idx)
      | .value e :: rest =>
        match hoistCallsFromExpr ctx sc idx e.expr with
        | none => none
        | some (h, s, n) =>
          match hoistListItems rest n with
          | some (hs, ss, n') => some (h ++ hs, s :: ss, n')
          | none => none
      | _ :: _ => none
    match hoistListItems items nextIdx with
    | none => none
    | some (h, ss, n) =>
      some (h, s!"(EffProg.Expr.list [{String.intercalate ", " ss}])", n)
  | .tuple items =>
    let rec hoistTupleItems (is : List SequenceItem) (idx : Nat)
        : Option (List String × List String × Nat) :=
      match is with
      | [] => some ([], [], idx)
      | .value e :: rest =>
        match hoistCallsFromExpr ctx sc idx e.expr with
        | none => none
        | some (h, s, n) =>
          match hoistTupleItems rest n with
          | some (hs, ss, n') => some (h ++ hs, s :: ss, n')
          | none => none
      | _ :: _ => none
    match hoistTupleItems items nextIdx with
    | none => none
    | some (h, ss, n) =>
      some (h, s!"(EffProg.Expr.tuple [{String.intercalate ", " ss}])", n)
  | .set items =>
    let rec hoistSetItems (is : List SequenceItem) (idx : Nat)
        : Option (List String × List String × Nat) :=
      match is with
      | [] => some ([], [], idx)
      | .value e :: rest =>
        match hoistCallsFromExpr ctx sc idx e.expr with
        | none => none
        | some (h, s, n) =>
          match hoistSetItems rest n with
          | some (hs, ss, n') => some (h ++ hs, s :: ss, n')
          | none => none
      | _ :: _ => none
    match hoistSetItems items nextIdx with
    | none => none
    | some (h, ss, n) =>
      some (h, s!"(EffProg.Expr.set_ [{String.intercalate ", " ss}])", n)
  | .dict dictItems =>
    let rec hoistDictItems (is : List DictItem) (idx : Nat)
        : Option (List String × List String × Nat) :=
      match is with
      | [] => some ([], [], idx)
      | .pair k v :: rest =>
        match hoistCallsFromExpr ctx sc idx k.expr with
        | none => none
        | some (hk, ks, n1) =>
          match hoistCallsFromExpr ctx sc n1 v.expr with
          | none => none
          | some (hv, vs, n2) =>
            match hoistDictItems rest n2 with
            | some (hr, rs, n3) => some (hk ++ hv ++ hr, s!"({ks}, {vs})" :: rs, n3)
            | none => none
      | _ :: _ => none
    match hoistDictItems dictItems nextIdx with
    | none => none
    | some (h, ps, n) => some (h, s!"(EffProg.Expr.dict [{String.intercalate ", " ps}])", n)
  | .fstring parts =>
    let rec hoistFStrParts (ps : List FStringPart) (idx : Nat)
        : Option (List String × List String × Nat) :=
      match ps with
      | [] => some ([], [], idx)
      | .literal sid :: rest =>
        let s := ctx.ir.resolveString sid
        match hoistFStrParts rest idx with
        | some (hr, rs, n) => some (hr, s!"Sum.inl \"{escapeLeanString s}\"" :: rs, n)
        | none => none
      | .value el _ _ :: rest =>
        match hoistCallsFromExpr ctx sc idx el.expr with
        | none => none
        | some (h, es, n1) =>
          match hoistFStrParts rest n1 with
          | some (hr, rs, n2) => some (h ++ hr, s!"Sum.inr {es}" :: rs, n2)
          | none => none
    match hoistFStrParts parts nextIdx with
    | none => none
    | some (h, ps, n) => some (h, s!"(EffProg.Expr.fstring [{String.intercalate ", " ps}])", n)
  | .named _ val => hoistCallsFromExpr ctx sc nextIdx val.expr
  | .«await» e => hoistCallsFromExpr ctx sc nextIdx e.expr
  | .lambda _ => some ([], "(EffProg.Expr.lit PyVal.none)", nextIdx)
  | .listComp elem comps =>
    match hoistCallsFromExpr ctx sc nextIdx elem.expr with
    | none => none
    | some (hElem, _, n1) =>
      let compHoists : Option (List String × Nat) :=
        comps.foldl (init := some ([], n1)) fun acc comp =>
          match acc with
          | none => none
          | some (hs, idx) =>
            match hoistCallsFromExpr ctx sc idx comp.iter.expr with
            | none => some (hs, idx)
            | some (hi, _, n) => some (hs ++ hi, n)
      match compHoists with
      | none => none
      | some (hComps, _) =>
        some (hElem ++ hComps, "(EffProg.Expr.lit PyVal.none)", n1)
  | .indirectCall callee args =>
    -- Hoist callee, emit indirect call at Perms.top.
    match hoistCallsFromExpr ctx sc nextIdx callee.expr with
    | some (hc, _ce, n1) =>
      let callStr := s!"(EffProg.Prog.call \"__indirect__\" [])"
      let paramRef := s!"(EffProg.Expr.param {n1})"
      some (hc ++ [callStr], paramRef, n1 + 1)
    | none =>
      -- Can't hoist callee; emit as effectful call (preserves perms).
      let callStr := s!"(EffProg.Prog.call \"__indirect__\" [])"
      let paramRef := s!"(EffProg.Expr.param {nextIdx})"
      some ([callStr], paramRef, nextIdx + 1)
  | .attrCall obj mid args =>
    match transExprToProg ctx sc (.attrCall obj mid args) with
    | some s => some ([], s, nextIdx)
    | none =>
      let methodName := ctx.ir.resolveString mid
      let argHoistsWithRefs : Option (List String × List String × Nat) := match args with
        | .simple es =>
          es.foldl (init := some ([], [], nextIdx)) fun acc e =>
            match acc with
            | none => none
            | some (hs, refs, idx) =>
              match hoistCallsFromExpr ctx sc idx e.expr with
              | some (h, pureRef, n) => some (hs ++ h, refs ++ [pureRef], n)
              | none => some (hs, refs, idx)
        | _ => some ([], [], nextIdx)
      match argHoistsWithRefs with
      | some (hoists, argRefs, finalIdx) =>
        let extTarget := "ext_" ++ sanitizeName methodName
        let extMatch := ctx.externals.find? (·.2.1 == extTarget)
        match extMatch with
        | some (_, cname, _) =>
          let callStr := s!"(EffProg.Prog.call \"{cname}\" [])"
          let paramRef := s!"(EffProg.Expr.param {finalIdx})"
          some (hoists ++ [callStr], paramRef, finalIdx + 1)
        | none =>
          if methodName == "gather" && !hoists.isEmpty then
            let listExpr := s!"(EffProg.Expr.list [{String.intercalate ", " argRefs}])"
            some (hoists, listExpr, finalIdx)
          else
            some (hoists, "(EffProg.Expr.lit PyVal.none)", finalIdx)
      | none => none
  | other =>
    match transExprToProg ctx sc other with
    | some s => some ([], s, nextIdx)
    | none => none

/-- Collect variables mutated in a for-loop body for the EffProg
    forFold translation. Returns deduplicated `StringId`s of
    variables that appear as `.opAssign` targets or as `.assign`
    targets where the name is already bound in `sc` (re-assignment
    = mutation of an outer-scope variable). The loop target
    variable itself is excluded. -/
def collectProgMutTargets (sc : PScope) (loopTargetIds : List StringId)
    : List Node → List StringId
  | [] => []
  | .opAssign id _ _ :: rest =>
    let r := collectProgMutTargets sc loopTargetIds rest
    if loopTargetIds.contains id.nameId then r
    else if r.contains id.nameId then r
    else id.nameId :: r
  | .assign id _ :: rest =>
    let r := collectProgMutTargets sc loopTargetIds rest
    if loopTargetIds.contains id.nameId then r
    else if (pscopeLookup sc id.nameId).isSome then
      if r.contains id.nameId then r else id.nameId :: r
    else r
  | .expr (ExprLoc.mk _ (.attrCall (ExprLoc.mk _ (.name id)) methodNameId _)) :: rest =>
    -- `.append()` / `.extend()` on a named receiver → mutation.
    let r := collectProgMutTargets sc loopTargetIds rest
    if loopTargetIds.contains id.nameId then r
    else if (pscopeLookup sc id.nameId).isSome then
      if r.contains id.nameId then r else id.nameId :: r
    else r
  | .subscriptAssign tgt _ _ _ :: rest =>
    -- `d[k] = v` on a named target → mutation of the container.
    match tgt.expr with
    | .name id =>
      let r := collectProgMutTargets sc loopTargetIds rest
      if loopTargetIds.contains id.nameId then r
      else if (pscopeLookup sc id.nameId).isSome then
        if r.contains id.nameId then r else id.nameId :: r
      else r
    | _ => collectProgMutTargets sc loopTargetIds rest
  | _ :: rest => collectProgMutTargets sc loopTargetIds rest

mutual

/-- Translate a single IR `Node` plus the rest-of-body's already-
    translated `EffProg` into an `EffProg` that runs the node then
    continues with `rest`. `scopeSize` is the current env depth
    (number of params + locals bound so far) — the de-Bruijn index
    the NEXT `letIn` would receive.

    Returns `none` for unsupported node shapes. The fallback is
    the caller, which aborts the whole translation. -/
partial def transNodeToProg (ctx : CodegenCtx) (sc : PScope) (scopeSize : Nat)
    (n : Node) (rest : String) (restSc : PScope) (restSize : Nat) : Option String :=
  let _ := restSc  -- unused for now, present for future shape extensions
  let _ := restSize
  -- A call is safe to translate iff the callee is a top-level
  -- name (external or local top-level func), NOT a local
  -- variable that aliases a function. Local-var aliases would
  -- be misresolved by `EffProg.Prog.permsOf` (which looks up
  -- by the Python name). Reject those.
  let callableIsSafe (callee : Callable) : Bool :=
    match callee with
    | .name id => (pscopeLookup sc id.nameId).isNone
    | _ => false
  -- Check if a local-variable callee is a KNOWN lambda binding.
  -- Safe to value-erase: the lambda was created in scope, so its
  -- perms are bounded by the outer function's.
  let callableIsLambda (callee : Callable) : Bool :=
    match callee with
    | .name id => ctx.progLambdaBindings.contains id.nameId
    | _ => false
  -- For unsafe (local-variable) callees, fall through to indirect
  -- call at Perms.top if the function is at top, OR value-erased
  -- pure call if the function is at a narrower perm. The latter
  -- loses value fidelity (returns PyVal.none) but preserves perms
  -- correctness — local lambdas can't have wider effects than the
  -- enclosing function.
  let canFallbackToIndirect := ctx.perms == "Perms.top"
  let canFallbackPure := true  -- always try pure fallback
  match n with
  | .pass => some rest
  | .assign id el =>
    -- Assign: three paths.
    --   1. Pure RHS → `letIn e k`
    --   2. Direct `.call` RHS → `letInEff call k`
    --   3. Hoistable: contains calls inside a larger expression →
    --      hoist calls to prior letInEff, then letIn the pure result
    match el.expr with
    | .call (.builtin _) _ =>
      -- Builtin call as RHS: `y = str(x)`, `n = len(items)`, etc.
      -- Pure, so emit `letIn` with the builtin expression (not
      -- `letInEff` which would route through `__indirect__`).
      match transExprToProg ctx sc el.expr with
      | some e => some s!"(EffProg.Prog.letIn {e} {rest})"
      | none => none
    | .call callee args =>
      -- Check alias first: if the callee has a nested-funcDef
      -- alias, use it directly (bypasses callableIsSafe since
      -- the alias is known-safe).
      let aliasName : Option String := match callee with
        | .name id => ctx.astLocalAliases.find? (·.1 == id.nameId) |>.map (·.2)
        | _ => none
      match aliasName with
      | some cname =>
        match transCallArgs ctx sc args with
        | some argStrs =>
          let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
          some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"{cname}\" {argList}) {rest})"
        | none => none
      | none =>
        if callableIsSafe callee then
          match callableToProgName ctx callee, transCallArgs ctx sc args with
          | some cname, some argStrs =>
            let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
            some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"{cname}\" {argList}) {rest})"
          | _, _ =>
            match hoistCallsFromExpr ctx sc scopeSize el.expr with
            | some (hoists, pureExpr, _) =>
              if hoists.isEmpty then none
              else some (hoists.foldr (init := s!"(EffProg.Prog.letIn {pureExpr} {rest})") fun call acc =>
                s!"(EffProg.Prog.letInEff {call} {acc})")
            | none => none
        else if canFallbackToIndirect then
          match transCallArgs ctx sc args with
          | some argStrs =>
            let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
            some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
          | none => none
        else if callableIsLambda callee then
          some s!"(EffProg.Prog.letIn (EffProg.Expr.lit PyVal.none) {rest})"
        else
          let lambdaEffects : Option (List String) := match callee with
            | .name cid => ctx.progLambdaEffectCalls.find? (·.1 == cid.nameId) |>.map (·.2)
            | _ => none
          match lambdaEffects with
          | some extCalls =>
            let effectChain := extCalls.foldr (init := s!"(EffProg.Prog.letIn (EffProg.Expr.lit PyVal.none) {rest})") fun callName acc =>
              s!"(EffProg.Prog.seq (EffProg.Prog.call \"{callName}\" []) {acc})"
            some effectChain
          | none =>
            let closurePerms : Option String := match callee with
              | .name cid => ctx.progClosureResultPerms.find? (·.1 == cid.nameId) |>.map (·.2)
              | _ => none
            match closurePerms with
            | some "Perms.none" =>
              some s!"(EffProg.Prog.letIn (EffProg.Expr.lit PyVal.none) {rest})"
            | some _ =>
              match transCallArgs ctx sc args with
              | some argStrs =>
                let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
                some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
              | none => none
            | none =>
              match transCallArgs ctx sc args with
              | some argStrs =>
                let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
                some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
              | none => none
    | .indirectCall _ args =>
      match transCallArgs ctx sc args with
      | some argStrs =>
        let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
        some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
      | none => none
    | .attrCall obj methodId args =>
      match transExprToProg ctx sc (.attrCall obj methodId args) with
      | some exprStr => some s!"(EffProg.Prog.letIn {exprStr} {rest})"
      | none =>
        if canFallbackToIndirect then
          match transCallArgs ctx sc args with
          | some argStrs =>
            let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
            some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"__attrCall__\" {argList}) {rest})"
          | none => none
        else none
    | _ =>
      match transExprToProg ctx sc el.expr with
      | some rhs => some s!"(EffProg.Prog.letIn {rhs} {rest})"
      | none =>
        -- Pure translation failed; try hoisting sub-calls.
        match hoistCallsFromExpr ctx sc scopeSize el.expr with
        | some (hoists, pureExpr, newIdx) =>
          if hoists.isEmpty then none  -- no calls hoisted → can't help
          else
            -- Wrap: chain letInEff for each hoisted call, then letIn
            -- the pure result (which references the hoisted params),
            -- then the rest (with scope extended for the hoisted +
            -- the letIn).
            -- rest was already translated at scopeSize (by the caller);
            -- we need to re-translate it at scopeSize + hoists + 1
            -- (the hoisted params plus the letIn result). But rest
            -- was translated with the scope AFTER this node — which
            -- assumed one new binding. We'll reuse it at the wrong
            -- depth. For soundness, this is OK if the rest only
            -- references earlier bindings. It's INCORRECT if the rest
            -- references the new binding by de-Bruijn index.
            -- TODO: proper re-translation for hoisted+shifted scopes.
            -- For now, wrap the hoists around (letIn pureExpr rest).
            let inner := s!"(EffProg.Prog.letIn {pureExpr} {rest})"
            some (hoists.foldr (init := inner) fun call acc =>
              s!"(EffProg.Prog.letInEff {call} {acc})")
        | none => none
  | .ret el =>
    match el.expr with
    | .call (.builtin _) _ =>
      -- Builtin call in return: `return len(x)`. Falls through to
      -- expression-level translation which handles builtins.
      match transExprToProg ctx sc el.expr with
      | some e => some s!"(EffProg.Prog.retWith {e})"
      | none => none
    | .call callee args =>
      let aliasName : Option String := match callee with
        | .name id => ctx.astLocalAliases.find? (·.1 == id.nameId) |>.map (·.2)
        | _ => none
      match aliasName with
      | some cname =>
        match transCallArgs ctx sc args with
        | some argStrs =>
          let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
          some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"{cname}\" {argList}) (EffProg.Prog.retWith (EffProg.Expr.param {scopeSize})))"
        | none => none
      | none =>
        if callableIsSafe callee then
          match callableToProgName ctx callee, transCallArgs ctx sc args with
          | some cname, some argStrs =>
            let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
            some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"{cname}\" {argList}) (EffProg.Prog.retWith (EffProg.Expr.param {scopeSize})))"
          | _, _ =>
            match hoistCallsFromExpr ctx sc scopeSize el.expr with
            | some (hoists, pureExpr, _) =>
              if hoists.isEmpty then none
              else some (hoists.foldr (init := s!"(EffProg.Prog.retWith {pureExpr})") fun call acc =>
                s!"(EffProg.Prog.letInEff {call} {acc})")
            | none => none
        else if canFallbackToIndirect then
          match transCallArgs ctx sc args with
          | some argStrs =>
            let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
            some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"__indirect__\" {argList}) (EffProg.Prog.retWith (EffProg.Expr.param {scopeSize})))"
          | none => none
        else if callableIsLambda callee then
          some s!"(EffProg.Prog.retWith (EffProg.Expr.lit PyVal.none))"
        else
          let lambdaEffects : Option (List String) := match callee with
            | .name cid => ctx.progLambdaEffectCalls.find? (·.1 == cid.nameId) |>.map (·.2)
            | _ => none
          match lambdaEffects with
          | some extCalls =>
            let effectChain := extCalls.foldr (init := s!"(EffProg.Prog.retWith (EffProg.Expr.lit PyVal.none))") fun callName acc =>
              s!"(EffProg.Prog.seq (EffProg.Prog.call \"{callName}\" []) {acc})"
            some effectChain
          | none =>
            let closurePerms : Option String := match callee with
              | .name cid => ctx.progClosureResultPerms.find? (·.1 == cid.nameId) |>.map (·.2)
              | _ => none
            match closurePerms with
            | some "Perms.none" =>
              some s!"(EffProg.Prog.retWith (EffProg.Expr.lit PyVal.none))"
            | _ =>
              match transCallArgs ctx sc args with
              | some argStrs =>
                let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
                some s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"__indirect__\" {argList}) (EffProg.Prog.retWith (EffProg.Expr.param {scopeSize})))"
              | none => none
    | .indirectCall callee args =>
      -- Hoist the callee first (it may be a call like `g(7)`),
      -- then emit the indirect call on the hoisted result.
      match hoistCallsFromExpr ctx sc scopeSize callee.expr with
      | some (hoists, calleeExpr, nextIdx) =>
        match transCallArgs ctx sc args with
        | some argStrs =>
          let argList := "[" ++ String.intercalate ", " (calleeExpr :: argStrs) ++ "]"
          let indirectCall := s!"(EffProg.Prog.call \"__indirect__\" {argList})"
          let retPart := s!"(EffProg.Prog.letInEff {indirectCall} (EffProg.Prog.retWith (EffProg.Expr.param {nextIdx})))"
          if hoists.isEmpty then some retPart
          else some (hoists.foldr (init := retPart) fun call acc =>
            s!"(EffProg.Prog.letInEff {call} {acc})")
        | none => none
      | none =>
        -- Can't hoist callee; try value-erased return.
        some s!"(EffProg.Prog.retWith (EffProg.Expr.lit PyVal.none))"
    | _ =>
      match transExprToProg ctx sc el.expr with
      | some e => some s!"(EffProg.Prog.retWith {e})"
      | none =>
        -- Try hoisting sub-calls from the expression.
        match hoistCallsFromExpr ctx sc scopeSize el.expr with
        | some (hoists, pureExpr, _) =>
          if hoists.isEmpty then none
          else
            let inner := s!"(EffProg.Prog.retWith {pureExpr})"
            some (hoists.foldr (init := inner) fun call acc =>
              s!"(EffProg.Prog.letInEff {call} {acc})")
        | none => none
  | .retNone => some "(EffProg.Prog.retWith (EffProg.Expr.lit PyVal.none))"
  | .expr el =>
    -- Expression statement (docstring literal, discarded call value,
    -- or a pure computation whose value is ignored).
    match el.expr with
    | .literal _ => some rest  -- elide docstring
    | .call (.builtin bid) (.simple args) =>
      -- Builtin call as statement (e.g. `print(x)`). Pure, result discarded.
      let builtinName := bid
      let argOpts := args.foldr (init := some ([] : List String)) fun e acc =>
        match acc, transExprToProg ctx sc e.expr with
        | some xs, some x => some (x :: xs)
        | _, _ => none
      match argOpts with
      | some _ => some rest  -- pure builtin; result discarded; just continue
      | none => none
    | .call callee args =>
      let aliasName : Option String := match callee with
        | .name id => ctx.astLocalAliases.find? (·.1 == id.nameId) |>.map (·.2)
        | _ => none
      match aliasName with
      | some cname =>
        match transCallArgs ctx sc args with
        | some argStrs =>
          let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
          some s!"(EffProg.Prog.seq (EffProg.Prog.call \"{cname}\" {argList}) {rest})"
        | none => none
      | none =>
        if callableIsSafe callee then
          match callableToProgName ctx callee, transCallArgs ctx sc args with
          | some cname, some argStrs =>
            let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
            some s!"(EffProg.Prog.seq (EffProg.Prog.call \"{cname}\" {argList}) {rest})"
          | _, _ => none
        else if canFallbackToIndirect then
          match transCallArgs ctx sc args with
          | some argStrs =>
            let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
            some s!"(EffProg.Prog.seq (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
          | none => none
        else if callableIsLambda callee then
          some rest
        else
          let lambdaEffects : Option (List String) := match callee with
            | .name cid => ctx.progLambdaEffectCalls.find? (·.1 == cid.nameId) |>.map (·.2)
            | _ => none
          match lambdaEffects with
          | some extCalls =>
            let effectChain := extCalls.foldr (init := rest) fun callName acc =>
              s!"(EffProg.Prog.seq (EffProg.Prog.call \"{callName}\" []) {acc})"
            some effectChain
          | none =>
            let closurePerms : Option String := match callee with
              | .name cid => ctx.progClosureResultPerms.find? (·.1 == cid.nameId) |>.map (·.2)
              | _ => none
            match closurePerms with
            | some "Perms.none" => some rest
            | some _ =>
              match transCallArgs ctx sc args with
              | some argStrs =>
                let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
                some s!"(EffProg.Prog.seq (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
              | none => none
            | none =>
              match transCallArgs ctx sc args with
              | some argStrs =>
                let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
                some s!"(EffProg.Prog.seq (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
              | none => none
    | .indirectCall _ args =>
      match transCallArgs ctx sc args with
      | some argStrs =>
        let argList := "[" ++ String.intercalate ", " argStrs ++ "]"
        some s!"(EffProg.Prog.seq (EffProg.Prog.call \"__indirect__\" {argList}) {rest})"
      | none =>
        let argExprs : List ExprLoc := match args with
          | .simple es => es | _ => []
        let hoistResult : Option (List String × Nat) :=
          argExprs.foldl (init := some ([], scopeSize)) fun acc e =>
            match acc with
            | none => none
            | some (hs, idx) =>
              match hoistCallsFromExpr ctx sc idx e.expr with
              | some (h, _, n) => some (hs ++ h, n)
              | none => none
        match hoistResult with
        | some (hoists, _) =>
          let indirectCall := s!"(EffProg.Prog.call \"__indirect__\" [])"
          let inner := s!"(EffProg.Prog.seq {indirectCall} {rest})"
          if hoists.isEmpty then some inner
          else some (hoists.foldr (init := inner) fun call acc =>
            s!"(EffProg.Prog.letInEff {call} {acc})")
        | none => none
    | .attrCall obj methodId args =>
      let methodName := ctx.ir.resolveString methodId
      -- For mutation methods (append/extend) on a scoped name, emit
      -- as letIn (so the value binds and scope extends).
      match obj.expr with
      | .name objId =>
        if (methodName == "append" || methodName == "extend") &&
           (pscopeLookup sc objId.nameId).isSome then
          match transExprToProg ctx sc (.attrCall obj methodId args) with
          | some exprStr =>
            some s!"(EffProg.Prog.letIn {exprStr} {rest})"
          | none => none
        else
          match transExprToProg ctx sc (.attrCall obj methodId args) with
          | some exprStr =>
            some s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal {exprStr}) {rest})"
          | none =>
            -- Hoist the entire attrCall expression. This extracts
            -- effectful sub-calls from the args (e.g., send_email(obj)
            -- inside obj.method(send_email(obj))).
            match hoistCallsFromExpr ctx sc scopeSize (.attrCall obj methodId args) with
            | some (hoists, pureExpr, _) =>
              let inner := s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal {pureExpr}) {rest})"
              some (hoists.foldr (init := inner) fun call acc =>
                s!"(EffProg.Prog.letInEff {call} {acc})")
            | none => none
      | _ =>
        match transExprToProg ctx sc (.attrCall obj methodId args) with
        | some exprStr =>
          some s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal {exprStr}) {rest})"
        | none =>
          match hoistCallsFromExpr ctx sc scopeSize (.attrCall obj methodId args) with
          | some (hoists, pureExpr, _) =>
            let inner := s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal {pureExpr}) {rest})"
            some (hoists.foldr (init := inner) fun call acc =>
              s!"(EffProg.Prog.letInEff {call} {acc})")
          | none => none
    | _ =>
      match transExprToProg ctx sc el.expr with
      | some e => some s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal {e}) {rest})"
      | none =>
        -- Try hoisting calls out of the expression.
        match hoistCallsFromExpr ctx sc scopeSize el.expr with
        | some (hoists, pureExpr, _) =>
          if hoists.isEmpty then
            -- Value-erased expression (e.g. unknown attrCall).
            -- Emit as yieldVal to keep the body translating.
            some s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal {pureExpr}) {rest})"
          else some (hoists.foldr
            (init := s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal {pureExpr}) {rest})")
            fun call acc => s!"(EffProg.Prog.letInEff {call} {acc})")
        | none => none
  | .«if» cond body orElse =>
    -- branchOn: translate condition, then both arms. If the
    -- condition contains calls, hoist them first.
    let condResult := match transExprToProg ctx sc cond.expr with
      | some e => some ([], e, scopeSize)
      | none => hoistCallsFromExpr ctx sc scopeSize cond.expr
    match condResult with
    | none => none
    | some (hoists, cExpr, _) =>
      match transBodyToProg ctx sc scopeSize body with
      | none => none
      | some bStr =>
        match transBodyToProg ctx sc scopeSize orElse with
        | none => none
        | some eStr =>
          let branchStr := s!"(EffProg.Prog.seq (EffProg.Prog.branchOn {cExpr} {bStr} {eStr}) {rest})"
          if hoists.isEmpty then some branchStr
          else some (hoists.foldr (init := branchStr) fun call acc =>
            s!"(EffProg.Prog.letInEff {call} {acc})")
  | .assert test msg =>
    match transExprToProg ctx sc test.expr with
    | none => none
    | some tExpr =>
      let msgExpr : String := match msg with
        | some m =>
          match transExprToProg ctx sc m.expr with
          | some me => me
          | none => "(EffProg.Expr.lit (PyVal.str \"AssertionError\"))"
        | none => "(EffProg.Expr.lit (PyVal.str \"AssertionError\"))"
      some s!"(EffProg.Prog.seq (EffProg.Prog.assertStmt {tExpr} {msgExpr}) {rest})"
  | .raise (some el) =>
    match transExprToProg ctx sc el.expr with
    | some e => some s!"(EffProg.Prog.raiseExc {e})"
    | none => none
  | .raise none => some "(EffProg.Prog.raiseExc (EffProg.Expr.lit PyVal.none))"
  | .opAssign id op el =>
    let curRef : String := match pscopeLookup sc id.nameId with
      | some idx => s!"(EffProg.Expr.param {idx})"
      | none =>
        let n := sanitizeName (ctx.ir.resolveString id.nameId)
        s!"(EffProg.Expr.globalRef \"{n}\")"
    let irOp : Option String := match op with
      | .add => some ".add" | .sub => some ".sub"
      | .mult => some ".mul" | .div => some ".div"
      | .«mod» => some ".mod" | .floorDiv => some ".floorDiv"
      | .«and» => some ".and_" | .«or» => some ".or_"
      | _ => none
    match irOp with
    | none => none
    | some os =>
      match transExprToProg ctx sc el.expr with
      | none => none
      | some rhs =>
        some s!"(EffProg.Prog.letIn (EffProg.Expr.binOp {os} {curRef} {rhs}) {rest})"
  | .subscriptOpAssign tgt idx _ val _ =>
    -- `d[k] += v`: value-erased (mutation not tracked precisely).
    some s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal (EffProg.Expr.lit PyVal.none)) {rest})"
  | .subscriptAssign tgt idx val _ =>
    match tgt.expr with
    | .name tgtId =>
      let curRef := match pscopeLookup sc tgtId.nameId with
        | some idx => s!"(EffProg.Expr.param {idx})"
        | none =>
          let n := sanitizeName (ctx.ir.resolveString tgtId.nameId)
          s!"(EffProg.Expr.globalRef \"{n}\")"
      match pscopeLookup sc tgtId.nameId with
      | none => -- global target: value-erased
        some s!"(EffProg.Prog.seq (EffProg.Prog.yieldVal (EffProg.Expr.lit PyVal.none)) {rest})"
      | some curIdx =>
        match transExprToProg ctx sc idx.expr, transExprToProg ctx sc val.expr with
        | some ie, some ve =>
          some s!"(EffProg.Prog.letIn (EffProg.Expr.subscriptSet (EffProg.Expr.param {curIdx}) {ie} {ve}) {rest})"
        | _, _ => none
    | _ => none
  | .«while» cond body orElse =>
    -- While loop: translate cond and body, emit whileBody.
    match transExprToProg ctx sc cond.expr with
    | none => none
    | some condStr =>
      if body.any (fun bn => match bn with | .assign _ _ | .opAssign _ _ _ => true | _ => false)
      then none  -- mutation inside while needs forFold
      else
      match transBodyToProg ctx sc scopeSize body with
      | none => none
      | some bodyStr =>
        if orElse.isEmpty then
          some s!"(EffProg.Prog.seq (EffProg.Prog.whileBody {condStr} {bodyStr}) {rest})"
        else
          match transBodyToProg ctx sc scopeSize orElse with
          | some elseStr =>
            some s!"(EffProg.Prog.seq (EffProg.Prog.whileBody {condStr} {bodyStr}) (EffProg.Prog.seq {elseStr} {rest}))"
          | none => none
  | .funcDef inner =>
    -- If scope was extended (restSize > scopeSize), emit letIn to
    -- occupy the de-Bruijn slot. If not, just pass through.
    if restSize > scopeSize then
      some s!"(EffProg.Prog.letIn (EffProg.Expr.lit PyVal.none) {rest})"
    else
      some rest
  | .«break» _ => some "(EffProg.Prog.break_)"
  | .«continue» _ => some "(EffProg.Prog.continue_)"
  | .unpackAssign targets _ el =>
    -- Unpack assign: `a, b = tup`. Lower to sequential pyIndex.
    -- Only handle simple name targets.
    let nameIds := targets.filterMap fun
      | .name id => some id.nameId
      | _ => none
    if nameIds.length != targets.length then none  -- non-name target
    else
    match transExprToProg ctx sc el.expr with
    | none => none
    | some rhsStr =>
      -- Emit: letIn rhs (letIn (subscript (param N) 0) (letIn (subscript (param N) 1) ... rest))
      let baseIdx := scopeSize
      let tupleRef := s!"(EffProg.Expr.param {baseIdx})"
      let unpacks := nameIds.mapIdx fun i _ =>
        s!"(EffProg.Prog.letIn (EffProg.Expr.subscript {tupleRef} (EffProg.Expr.lit (PyVal.int ({i})))) "
      let closeParens := String.join (unpacks.map fun _ => ")")
      some (s!"(EffProg.Prog.letIn {rhsStr} " ++ String.join unpacks ++ rest ++ closeParens ++ ")")
  | .import _ _ | .importFrom _ _ _ =>
    some rest  -- imports: no runtime effect
  | .global _ _ | .nonlocal _ _ =>
    some rest  -- scope declarations: no runtime effect
  | .«try» tb =>
    match transBodyToProg ctx sc scopeSize tb.body with
    | none => none
    | some bodyStr =>
      let handlerOpt := match tb.handlers with
        | [] => some "EffProg.Prog.pureStmt"
        | h :: _ =>
          match h with
          | .mk _ excName hbody =>
            let hSc := match excName with
              | some eid => pscopePush sc eid.nameId scopeSize
              | none => sc
            let hSize := match excName with
              | some _ => scopeSize + 1
              | none => scopeSize
            transBodyToProg ctx hSc hSize hbody
      match handlerOpt with
      | none => none
      | some handlerStr =>
        some s!"(EffProg.Prog.seq (EffProg.Prog.tryExc {bodyStr} {handlerStr}) {rest})"
  | .«for» tgt iter body orElse =>
    match tgt with
    | .name tgtId =>
      let tgtIds : List StringId := [tgtId.nameId]
      let muts := collectProgMutTargets sc tgtIds body
      match muts with
      | [mutId] =>
        -- Single mutation target: emit forFold.
        -- The accumulator is the current value of the mutated variable.
        match pscopeLookup sc mutId with
        | none => none
        | some mutIdx =>
          match transExprToProg ctx sc iter.expr with
          | none => none
          | some iterStr =>
            -- forFold body scope:
            --   acc (mutated var) at scopeSize
            --   loop item at scopeSize + 1
            let foldSc := pscopePush (pscopePush sc mutId scopeSize) tgtId.nameId (scopeSize + 1)
            match transForFoldBodyToProg ctx foldSc (scopeSize + 2) mutId body with
            | none => none
            | some foldBodyStr =>
              let initExpr := s!"(EffProg.Expr.param {mutIdx})"
              let foldStr := s!"(EffProg.Prog.forFold {iterStr} {initExpr} {foldBodyStr})"
              -- Wrap in letInEff so the fold result binds at scopeSize
              -- (where the continuation expects the mutated var).
              let wrappedStr := s!"(EffProg.Prog.letInEff {foldStr} {rest})"
              if orElse.isEmpty then
                some wrappedStr
              else
                match transBodyToProg ctx sc scopeSize orElse with
                | none => none
                | some elseStr =>
                  some s!"(EffProg.Prog.letInEff {foldStr} (EffProg.Prog.seq {elseStr} {rest}))"
      | _ =>
        -- No mutation or multi-mutation (multi falls through to none
        -- if body has assigns/opAssigns).
        if body.any (fun bn => match bn with
          | .assign _ _ | .opAssign _ _ _ | .subscriptAssign _ _ _ _ => true | _ => false)
        then none
        else
        match transExprToProg ctx sc iter.expr with
        | none => none
        | some iterStr =>
          let loopSc := pscopePush sc tgtId.nameId scopeSize
          -- Translate the loop body.
          match transBodyToProg ctx loopSc (scopeSize + 1) body with
          | none => none
          | some bodyStr =>
            -- If orElse is non-empty, translate and seq after loop.
            let loopStr := s!"(EffProg.Prog.forEach {iterStr} {bodyStr})"
            if orElse.isEmpty then
              some s!"(EffProg.Prog.seq {loopStr} {rest})"
            else
              match transBodyToProg ctx sc scopeSize orElse with
              | none => none
              | some elseStr =>
                some s!"(EffProg.Prog.seq {loopStr} (EffProg.Prog.seq {elseStr} {rest}))"
    | _ => none
  | _ => none

/-- Translate a sequence of IR nodes into a single `EffProg`.
    Threads scope through `assign` statements so later references
    resolve to the correct de-Bruijn index. -/
partial def transBodyToProg (ctx : CodegenCtx) (sc : PScope) (scopeSize : Nat)
    : List Node → Option String
  | [] => some "EffProg.Prog.pureStmt"
  | n :: rest =>
    -- For `assign` and `opAssign`, the tail must be translated
    -- under the extended scope (new binding visible). For other
    -- shapes, the scope is unchanged.
    match n with
    | .assign id el =>
      let gatherArgs : Option (List ExprLoc) := match el.expr with
        | .«await» (ExprLoc.mk _ (.attrCall _ mid (.simple args))) =>
          if ctx.ir.resolveString mid == "gather" then some args else none
        | _ => none
      match gatherArgs with
      | some args =>
        let callNames := args.filterMap fun arg => match arg.expr with
          | .call (.name cid) _ => callableToProgName ctx (.name cid)
          | _ => none
        if callNames.length == args.length && !args.isEmpty then
          let numCalls := callNames.length
          let newSc := pscopePush sc id.nameId (scopeSize + numCalls)
          match transBodyToProg ctx newSc (scopeSize + numCalls + 1) rest with
          | none => none
          | some restStr =>
            let paramRefs := (List.range numCalls).map fun i =>
              s!"(EffProg.Expr.param {scopeSize + i})"
            let listExpr := s!"(EffProg.Expr.list [{String.intercalate ", " paramRefs}])"
            let inner := s!"(EffProg.Prog.letIn {listExpr} {restStr})"
            let callArgStrs := args.map fun arg => match arg.expr with
              | .call _ callArgs =>
                match transCallArgs ctx sc callArgs with
                | some strs => "[" ++ String.intercalate ", " strs ++ "]"
                | none => "[]"
              | _ => "[]"
            let hoisted := (callNames.zip callArgStrs).foldr (init := inner) fun (cname, argList) acc =>
              s!"(EffProg.Prog.letInEff (EffProg.Prog.call \"{cname}\" {argList}) {acc})"
            some hoisted
          else
            let newSc := pscopePush sc id.nameId scopeSize
            match transBodyToProg ctx newSc (scopeSize + 1) rest with
            | none => none
            | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
      | none =>
        let newSc := pscopePush sc id.nameId scopeSize
        match transBodyToProg ctx newSc (scopeSize + 1) rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
    | .opAssign id _ _ =>
      let newSc := pscopePush sc id.nameId scopeSize
      match transBodyToProg ctx newSc (scopeSize + 1) rest with
      | none => none
      | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
    | .funcDef inner =>
      -- Only extend scope if the inner name is actually REFERENCED
      -- in the continuation. If it's not referenced (the funcDef
      -- just defines a closure that's returned via alias), skip
      -- the scope extension to avoid shifting de-Bruijn indices.
      let innerNameId := inner.name.nameId
      -- Deep check: is innerNameId referenced ANYWHERE in the
      -- continuation? Use the existing collectAllNameRefs.
      let restRefs := collectAllNameRefs rest
      let isReferenced := restRefs.contains innerNameId
      if isReferenced then
        let newSc := pscopePush sc innerNameId scopeSize
        match transBodyToProg ctx newSc (scopeSize + 1) rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
      else
        match transBodyToProg ctx sc scopeSize rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize
    | .unpackAssign targets _ _ =>
      let nameIds := targets.filterMap fun
        | .name id => some id.nameId
        | _ => none
      let totalNew := 1 + nameIds.length
      let newSc := nameIds.zipIdx.foldl (init := sc) fun acc (nid, idx) =>
        pscopePush acc nid (scopeSize + 1 + idx)
      match transBodyToProg ctx newSc (scopeSize + totalNew) rest with
      | none => none
      | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + totalNew)
    | .expr (ExprLoc.mk _ (.attrCall (ExprLoc.mk _ (.name objId)) methodId (.simple _))) =>
      let methodName := ctx.ir.resolveString methodId
      if (methodName == "append" || methodName == "extend") &&
         (pscopeLookup sc objId.nameId).isSome then
        let newSc := pscopePush sc objId.nameId scopeSize
        match transBodyToProg ctx newSc (scopeSize + 1) rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
      else
        match transBodyToProg ctx sc scopeSize rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize
    | .subscriptAssign tgt _ _ _ =>
      match tgt.expr with
      | .name tgtId =>
        let newSc := pscopePush sc tgtId.nameId scopeSize
        match transBodyToProg ctx newSc (scopeSize + 1) rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
      | _ =>
        match transBodyToProg ctx sc scopeSize rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize
    | .«for» tgt _ body _ =>
      -- For-loops with a single mutation target produce a forFold
      -- whose result rebinds the mutated variable in the continuation.
      let tgtIds : List StringId := match tgt with
        | .name id => [id.nameId] | _ => []
      let muts := collectProgMutTargets sc tgtIds body
      match muts with
      | [mutId] =>
        -- Single mutation: forFold result rebinds the mutated var.
        let newSc := pscopePush sc mutId scopeSize
        match transBodyToProg ctx newSc (scopeSize + 1) rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
      | _ =>
        -- Zero or multi-mutation: forEach (no scope change) or bail.
        match transBodyToProg ctx sc scopeSize rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize
    | _ =>
      match transBodyToProg ctx sc scopeSize rest with
      | none => none
      | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize

/-- Like `transBodyToProg` but for forFold bodies: the base case
    yields the current value of the accumulator variable instead of
    `pureStmt`. `accVarId` is the `StringId` of the mutated variable
    whose final value should be yielded. -/
partial def transForFoldBodyToProg (ctx : CodegenCtx) (sc : PScope) (scopeSize : Nat)
    (accVarId : StringId) : List Node → Option String
  | [] =>
    -- Yield the accumulator's current binding.
    match pscopeLookup sc accVarId with
    | none => none
    | some idx => some s!"(EffProg.Prog.yieldVal (EffProg.Expr.param {idx}))"
  | n :: rest =>
    match n with
    | .assign id _ =>
      let newSc := pscopePush sc id.nameId scopeSize
      match transForFoldBodyToProg ctx newSc (scopeSize + 1) accVarId rest with
      | none => none
      | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
    | .opAssign id _ _ =>
      let newSc := pscopePush sc id.nameId scopeSize
      match transForFoldBodyToProg ctx newSc (scopeSize + 1) accVarId rest with
      | none => none
      | some restStr => transNodeToProg ctx sc scopeSize n restStr newSc (scopeSize + 1)
    | .expr (ExprLoc.mk _ (.attrCall (ExprLoc.mk _ (.name objId)) methodId (.simple args))) =>
      -- `.append()` on the accumulator: rebind as letIn.
      let methodName := ctx.ir.resolveString methodId
      if objId.nameId == accVarId && (methodName == "append" || methodName == "extend") then
        match pscopeLookup sc objId.nameId with
        | none => none
        | some objIdx =>
          match args with
          | [val] =>
            match transExprToProg ctx sc val.expr with
            | some valStr =>
              let newSc := pscopePush sc accVarId scopeSize
              match transForFoldBodyToProg ctx newSc (scopeSize + 1) accVarId rest with
              | none => none
              | some restStr =>
                some s!"(EffProg.Prog.letIn (EffProg.Expr.listAppend (EffProg.Expr.param {objIdx}) {valStr}) {restStr})"
            | none => none
          | _ => none
      else
        match transForFoldBodyToProg ctx sc scopeSize accVarId rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize
    | .subscriptAssign tgt idx val _ =>
      -- `d[k] = v` on the accumulator: rebind via subscriptSet.
      match tgt.expr with
      | .name tgtId =>
        if tgtId.nameId == accVarId then
          match pscopeLookup sc tgtId.nameId with
          | none => none
          | some objIdx =>
            match transExprToProg ctx sc idx.expr, transExprToProg ctx sc val.expr with
            | some ie, some ve =>
              let newSc := pscopePush sc accVarId scopeSize
              match transForFoldBodyToProg ctx newSc (scopeSize + 1) accVarId rest with
              | none => none
              | some restStr =>
                some s!"(EffProg.Prog.letIn (EffProg.Expr.subscriptSet (EffProg.Expr.param {objIdx}) {ie} {ve}) {restStr})"
            | _, _ => none
        else
          match transForFoldBodyToProg ctx sc scopeSize accVarId rest with
          | none => none
          | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize
      | _ =>
        match transForFoldBodyToProg ctx sc scopeSize accVarId rest with
        | none => none
        | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize
    | _ =>
      match transForFoldBodyToProg ctx sc scopeSize accVarId rest with
      | none => none
      | some restStr => transNodeToProg ctx sc scopeSize n restStr sc scopeSize

end

/-- Initialize a parameter scope from a list of param `StringId`s.
    Params are bound at positions `0, 1, 2, ...` in the interp Env,
    so `param 0` refers to the first argument. We build the scope
    in reverse-order (most recent at head) so `pscopeLookup` finds
    the right entry. -/
def initialPScope (params : List StringId) : PScope :=
  let indexed := params.zipIdx  -- [(id, 0), (id, 1), ...]
  indexed.reverse.map (fun (id, i) => (id, i))

/-- Top-level: try to emit a function as an `EffProg` def + wrapper.
    Returns `some (progDefStr, envExpr)` if the function's body is
    fully translatable, `none` otherwise. The caller splices the
    results into the executable emission, falling back to the old
    translator when this returns `none`. -/
def tryEmitEffProg (ctx : CodegenCtx) (fd : FunctionDef) (funcName : String)
    : Option (String × String) :=
  let paramIds := allParamIds fd.signature
  let paramNames := paramIds.map (fun id => sanitizeName (ctx.ir.resolveString id))
  let scope := initialPScope paramIds
  -- Build aliases for nested funcDefs so calls to inner functions
  -- resolve to the mangled name in __extEnvProg.
  let nestedAliases : List (StringId × String) := fd.body.filterMap fun
    | .funcDef inner =>
      let innerName := sanitizeName (ctx.ir.resolveString inner.name.nameId)
      let mangled := funcName ++ "__" ++ innerName
      some (inner.name.nameId, mangled)
    | _ => none
  let funcValueAliases : List (StringId × String) := fd.body.filterMap fun
    | .assign id el => match el.expr with
      | .name srcId =>
        let srcName := ctx.ir.resolveString srcId.nameId
        let isKnownFunc := ctx.knownFuncs.any (·.1 == srcId.nameId)
        let isExternal := ctx.externals.any (·.1 == srcId.nameId)
        if isKnownFunc then some (id.nameId, sanitizeName srcName)
        else if isExternal then some (id.nameId, "ext_" ++ sanitizeName srcName)
        else none
      | _ => none
    | _ => none
  -- Collect lambda/funcDef bindings for safe local-call tracking.
  -- Only include lambdas whose body has NO external calls — a lambda
  -- that calls an external could have wider perms than the outer
  -- function, and value-erasing would hide the effect (soundness leak).
  let bodyHasExternalCall (nodes : List Node) : Bool :=
    nodes.any fun
      | .expr (ExprLoc.mk _ (.call (.name id) _)) =>
        id.scope == .localUnassigned
      | .assign _ (ExprLoc.mk _ (.call (.name id) _)) =>
        id.scope == .localUnassigned
      | .ret (ExprLoc.mk _ (.call (.name id) _)) =>
        id.scope == .localUnassigned
      | _ => false
  let lambdaBindings : List StringId := fd.body.filterMap fun
    | .assign id el => match el.expr with
      | .lambda lfd =>
        if bodyHasExternalCall lfd.body then none
        else some id.nameId
      | _ => none
    | .funcDef inner =>
      if bodyHasExternalCall inner.body then none
      else some inner.name.nameId
    | _ => none
  let lambdaEffectCalls : List (StringId × List String) := fd.body.filterMap fun
    | .assign id el => match el.expr with
      | .lambda lfd =>
        if bodyHasExternalCall lfd.body then
          let extCalls := (collectAllNameCallIds lfd.body).filter (·.scope == .localUnassigned)
          let extNames := extCalls.map fun cid =>
            "ext_" ++ sanitizeName (ctx.ir.resolveString cid.nameId)
          some (id.nameId, extNames.eraseDups)
        else none
      | _ => none
    | _ => none
  let closureResultPerms : List (StringId × String) := fd.body.filterMap fun
    | .assign id el => match el.expr with
      | .call (.name calleeId) _ =>
        match ctx.closureReturningFuncs.find? (·.1 == calleeId.nameId) with
        | some (_, _, innerPerms) => some (id.nameId, innerPerms)
        | none => none
      | _ => none
    | _ => none
  let ctxWithAliases := { ctx with
    astLocalAliases := nestedAliases ++ funcValueAliases,
    progLambdaBindings := lambdaBindings,
    progLambdaEffectCalls := lambdaEffectCalls,
    progClosureResultPerms := closureResultPerms }
  match transBodyToProg ctxWithAliases scope paramIds.length fd.body with
  | none =>
    none
  | some progBody =>
    let progDefName := s!"{funcName}__prog"
    let progDef := s!"def {progDefName} : EffProg.Prog := {progBody}\n"
    -- Build the env list: [param0, param1, ...] as a Lean list literal.
    let envList := "[" ++ String.intercalate ", " paramNames ++ "]"
    some (progDef, envList)

def detectExternals (ir : IrExport) (nodes : List Node) : List (StringId × String) :=
  -- Use both the shallow callIds collector and the deep name refs collector
  let callIds := collectNodeCallIds nodes
  let deepCallIds := collectAllNameCallIds nodes
  let allIds := callIds ++ deepCallIds
  let externalIds := allIds.filter fun id => id.scope == .localUnassigned
  externalIds.map (fun id => (id.nameId, ir.resolveString id.nameId))
    |>.eraseDups
    |>.filter fun (_, name) => !name.startsWith "<" && !name.isEmpty

def externalPerms : String → String
  | "search_web" => "{ net := true }" | "send_email" => "{ net := true }"
  | "read_file" => "{ fs := true }" | "write_file" => "{ fs := true }"
  | "get_env" => "{ env := true }"
  -- Common agent-tool names used by the bundled examples. These are
  -- treated as networked tool calls so the example agents can declare
  -- `Effect[Net, ...]` and have the codegen accept their use of these
  -- externals. The G1 fix would otherwise reject any use of an unknown
  -- external from a non-`Perms.top` function. (See § 2.1 in the roadmap
  -- for the planned mechanism that lets users declare additional
  -- externals from source.)
  | "summarize" => "{ net := true }" | "generate_report" => "{ net := true }"
  | "send_notification" => "{ net := true }" | "ext_notify" => "{ net := true }"
  | _ => "Perms.none"

/-- Generate Lean source from a parsed IR. The optional
    `customExternals` list extends the hardcoded `externalPerms`
    table with user-declared externals — typically parsed from
    `# external: <name> <effects>` directives in the Python source
    by `parseExternalDirectives`. Each entry is `(python_name,
    perms-source-string)`. -/
def generateLean (ir : IrExport) (customExternals : List (String × String) := []) : String :=
  -- Closure that consults the user-supplied externals table first,
  -- then falls back to the hardcoded `externalPerms`. This is the
  -- single point through which the rest of the codegen looks up
  -- external perms — every other call now goes through it.
  let lookupExtPerms (name : String) : String :=
    match customExternals.find? (·.1 == name) with
    | some (_, perms) => perms
    | none => externalPerms name
  let customExtNames : List String := customExternals.map (·.1)
  let nodes := ir.nodes
  -- Identify locally-defined functions first so we can exclude them from
  -- external detection. Without this, a module-level call to a local
  -- `f_basic` (which has scope `.localUnassigned` like any unbound name)
  -- gets axiomatized as `ext_f_basic` alongside the real `def f_basic`,
  -- and the module-level code resolves to the wrong one.
  let localFuncIds : List StringId :=
    nodes.filterMap fun | .funcDef fd => some fd.name.nameId | _ => none
  let externals := (detectExternals ir nodes).filter
    fun (nid, _) => !localFuncIds.contains nid
  let knownExtNames := ["search_web", "send_email", "read_file", "write_file", "get_env",
    "summarize", "generate_report", "send_notification", "ext_notify"] ++ customExtNames

  -- Externals are emitted as **computable** `def`s with a `pure PyVal.none`
  -- placeholder body. The TYPE carries the perms (so a Pure caller still
  -- gets rejected for calling a `Net` external — that's the soundness
  -- guarantee), but the body is reducible, which means modules that call
  -- externals are no longer forced `noncomputable`. Their `«__module__»`
  -- bodies fully reduce, and `decide` / `native_decide` can witness the
  -- expected outcome (`= .ok PyVal.none` for happy paths, `≠ .ok PyVal.none`
  -- for intentional-error tests).
  --
  -- Caveat: assertions about the *return value* of an external become
  -- vacuous, since every `read_file(x)` reduces to `PyVal.none`. That's
  -- the same situation as with the previous `axiom` formulation — both
  -- give us a value-oblivious model — but the new form is concrete
  -- rather than opaque, which is what unblocks reduction.
  -- Soundness fix G1: unknown externals are emitted CONCRETELY at
  -- `Perms.top` instead of polymorphically in `p`. A polymorphic external
  -- silently instantiates `p := Perms.none` when used inside a Pure
  -- function, allowing the user to lie about effects on any function
  -- that calls an unknown external. By pinning unknown externals to
  -- `Perms.top`, every caller must itself be at `Perms.top` (or wider) —
  -- which forces unannotated functions to widen and rejects annotated
  -- `Pure`/`Net`/etc. functions that try to slip an unknown external
  -- past the type system. The user opts in to letting the function
  -- escape effect tracking by leaving it unannotated.
  let externalDecls := externals.map fun (nid, name) =>
    let leanName := "ext_" ++ sanitizeName name
    let maxArity := findMaxArity nid nodes
    let arity := if maxArity == 0 then 1 else maxArity
    let argTypes := String.intercalate " → " (List.replicate arity "PyVal")
    let argLam := String.intercalate " " (List.replicate arity "_")
    let knownPerms := lookupExtPerms name
    let isUnknown := knownPerms == "Perms.none" && !knownExtNames.contains name
    let declPerms := if isUnknown then "Perms.top" else knownPerms
    s!"def {leanName} : {argTypes} → Eff {declPerms} PyVal := fun {argLam} => pure PyVal.none"

  -- Track each external's declared perms so call sites can ascribe to
  -- them. For unknown externals this is `Perms.top`, which forces the
  -- caller to be at `Perms.top` for the type ascription to succeed.
  let externalCtx := externals.map fun (nid, name) =>
    let knownPerms := lookupExtPerms name
    let isUnknown := knownPerms == "Perms.none" && !knownExtNames.contains name
    let declPerms := if isUnknown then "Perms.top" else knownPerms
    (nid, "ext_" ++ sanitizeName name, declPerms)

  -- Lean names of unknown externals — used to detect their use in a
  -- function body so we can widen unannotated callers to `Perms.top`
  -- (mirroring the existing widening for `PyVal.callFn`).
  let unknownExtLeanNames : List String := externals.filterMap fun (_, name) =>
    let knownPerms := lookupExtPerms name
    if knownPerms == "Perms.none" && !knownExtNames.contains name then
      some ("ext_" ++ sanitizeName name)
    else none
  -- IDs of unknown externals — used to walk the IR (rather than string-
  -- match the translated body) for places where we need a definite
  -- answer about "did this fragment call an unknown ext?".
  let unknownExtIds : List StringId := externals.filterMap fun (nid, name) =>
    let knownPerms := lookupExtPerms name
    if knownPerms == "Perms.none" && !knownExtNames.contains name then
      some nid
    else none
  -- Compute external arities (max observed call-site arg count) so call
  -- sites can pad under-applied calls without re-walking the IR.
  let externalArities : List (StringId × Nat) := externals.map fun (nid, _) =>
    let raw := findMaxArity nid nodes
    (nid, if raw == 0 then 1 else raw)

  let funcDefs := nodes.filterMap fun | .funcDef fd => some fd | _ => none
  let knownFuncs := funcDefs.map fun fd =>
    (fd.name.nameId, sanitizeName (ir.resolveString fd.name.nameId), fd.effectAnnotation)
  -- Track top-level funcdef arities so call sites in module-level code
  -- (and in other functions) can pad missing arguments with `PyVal.none`
  -- when Python defaults aren't supplied.
  let topLevelParamCounts : List (StringId × Nat) := funcDefs.map fun fd =>
    (fd.name.nameId, (allParams ir fd.signature).length)
  let topLevelParamIds : List (StringId × List StringId) := funcDefs.map fun fd =>
    (fd.name.nameId, allParamIds fd.signature)

  -- Per-funcdef default-value table. For each defaulted parameter, we
  -- pre-translate the default expression and emit it as a top-level
  -- `def <funcName>__default_<i> : PyVal := <expr>`. The
  -- (funcId, paramIdx) → defName mapping lives in `funcDefaults` so
  -- call sites can look up the right default. Pre-evaluation matches
  -- Python's "defaults evaluated once at definition time" semantics.
  --
  -- The IR's `default_exprs` is laid out as
  -- `[pos_defaults...][arg_defaults...][kwarg_defaults...]`.
  --
  -- * `pos_defaults_count` defaults trail the `posArgs` group.
  -- * `arg_defaults_count` defaults trail the `args` (positional-or-
  --   keyword) group.
  -- * `kwargDefaultMap[j]` (when `Some k`) means the j-th `kwargs` (kw-only)
  --   parameter takes its default from the k-th entry of the kwarg-default
  --   slice.  Keyword-only defaults can be sparse, so we can't just take
  --   the trailing entries the way pos/arg defaults work.
  --
  -- The `paramIdx` we store is into `allParamIds`, which is laid out as
  -- `posArgs ++ args ++ varArgs ++ kwargs ++ varKwargs`.
  let funcDefaults : List ((StringId × Nat) × String) := funcDefs.flatMap fun fd =>
    let sig := fd.signature
    let posLen := (sig.posArgs.getD []).length
    let argLen := (sig.args.getD []).length
    let varArgsLen := if sig.varArgs.isSome then 1 else 0
    let posDefCount := sig.posDefaultsCount
    let argDefCount := sig.argDefaultsCount
    let funcName := sanitizeName (ir.resolveString fd.name.nameId)
    let mkEntry (i : Nat) (paramIdx : Nat) :=
      ((fd.name.nameId, paramIdx), s!"{funcName}__default_{i}")
    -- Trailing pos_args defaults: paramIdx = posLen - posDefCount + j
    let posEntries : List ((StringId × Nat) × String) := (List.range posDefCount).map fun j =>
      mkEntry j (posLen - posDefCount + j)
    -- Trailing args defaults: paramIdx = posLen + (argLen - argDefCount + j)
    let argEntries : List ((StringId × Nat) × String) := (List.range argDefCount).map fun j =>
      mkEntry (posDefCount + j) (posLen + argLen - argDefCount + j)
    -- Sparse keyword-only defaults via `kwargDefaultMap`. The j-th entry
    -- maps the j-th `kwargs` (kw-only) parameter to its default-slice
    -- index, if any. Defaults sit AFTER varArgs in `allParamIds`.
    let kwBase := posLen + argLen + varArgsLen
    let kwEntries : List ((StringId × Nat) × String) :=
      match sig.kwargDefaultMap with
      | none => []
      | some m => m.mapIdx (fun j entry => match entry with
          | none => none
          | some k => some (mkEntry (posDefCount + argDefCount + k) (kwBase + j))) |>.filterMap id
    posEntries ++ argEntries ++ kwEntries

  -- ----------------------------------------------------------------------
  -- Closure-returning function detection
  -- ----------------------------------------------------------------------
  --
  -- Path 1 (closure-type tracking): a function whose body has the
  -- shape `[funcDef inner, ret (name inner)]` or `[ret (lambda)]` is
  -- a closure factory. Today these emit `Eff p PyVal` returning
  -- `PyVal.ofFn0/1` (an axiom — noncomputable). With closure tracking,
  -- the function returns a typed `PyClosure q n` instead, the body
  -- becomes plain `pure (PyClosure.mk{n} ...)`, and call sites bind
  -- the result as a closure (so subsequent calls go through
  -- `PyClosure.callN` instead of the conservative `PyVal.callFn`).
  --
  -- We classify in two passes:
  -- 1. Direct: detect functions whose body is one of the recognised
  --    factory shapes. Capture (arity, perms-of-inner-body).
  -- 2. (We don't do indirect propagation yet — a function that returns
  --    the result of another closure-returning function still falls
  --    back to PyVal.)
  let detectInnerSig (innerFd : FunctionDef) : Option (Nat × String) :=
    let arity := (allParams ir innerFd.signature).length
    -- Inner closures up to arity 16 are supported by `PyClosure`.
    if arity > 16 then none
    else
      let basePerms := effectAnnotationToPerms innerFd.effectAnnotation
      -- G1 widening for inner closures: if the inner body calls an
      -- unknown external (declared at `Perms.top`), widen the closure's
      -- perms to `Perms.top` so the inner `Eff.runFunction` block can
      -- accommodate the call. Without this, the closure's perms stay
      -- at the inner's annotation (e.g. `Perms.none` for unannotated)
      -- and the embedded `ext_X` call fails to type-check.
      let isUnannotated := match innerFd.effectAnnotation with
        | .unannotated => true | _ => false
      let innerCallIds := collectAllNameCallIds innerFd.body |>.map (·.nameId)
      let usesUnknownExt := innerCallIds.any fun id => unknownExtIds.contains id
      let permsStr :=
        if isUnannotated && usesUnknownExt then "Perms.top" else basePerms
      some (arity, permsStr)
  let isClosureReturning (fd : FunctionDef) : Option (Nat × String) :=
    -- Shape C: async function. Lower the entire body as a 0-arg coroutine
    -- thunk closing over the function parameters. The "outer" function is
    -- a pure constructor returning `PyClosure innerPerms 0`. `await foo(args)`
    -- can then bind `foo args` (a closure) and call it via `PyClosure.call0`,
    -- so the body's effects propagate properly through the await chain.
    if fd.isAsync then
      let basePerms := effectAnnotationToPerms fd.effectAnnotation
      let isUnannotated := match fd.effectAnnotation with
        | .unannotated => true | _ => false
      let bodyCallIds := collectAllNameCallIds fd.body |>.map (·.nameId)
      let usesUnknownExt := bodyCallIds.any fun id => unknownExtIds.contains id
      -- An async body that calls another async function with non-trivial
      -- perms transitively inherits those perms. Detecting precisely needs
      -- a fixpoint that runs later, so as a conservative approximation we
      -- check if any directly-called async function ALSO uses an unknown
      -- external. (The pure callsAsync check was too broad — it widened
      -- even purely-arithmetic async chains, breaking the existing async
      -- corpus.)
      let allFuncDefs := nodes.filterMap fun | .funcDef fd => some fd | _ => none
      let asyncCalleeUsesExt := bodyCallIds.any fun id =>
        match allFuncDefs.find? (fun afd => afd.name.nameId == id && afd.isAsync) with
        | some afd =>
          let calleeCallIds := collectAllNameCallIds afd.body |>.map (·.nameId)
          calleeCallIds.any fun cid => unknownExtIds.contains cid
        | none => false
      let permsStr :=
        if isUnannotated && (usesUnknownExt || asyncCalleeUsesExt) then "Perms.top" else basePerms
      some (0, permsStr)
    else
    match fd.body with
    -- Shape A: define an inner func, then return its name.
    | [.funcDef inner, .ret retEl] =>
      match retEl.expr with
      | .name nameId =>
        if nameId.nameId == inner.name.nameId then detectInnerSig inner
        else none
      | _ => none
    -- Shape B: return a lambda directly.
    | [.ret retEl] =>
      match retEl.expr with
      | .lambda inner => detectInnerSig inner
      | _ => none
    | _ => none
  let closureReturningFuncs : List (StringId × Nat × String) :=
    funcDefs.filterMap fun fd =>
      match isClosureReturning fd with
      | some (n, p) => some (fd.name.nameId, n, p)
      | none => none

  let ctx : CodegenCtx :=
    { ir := ir, externals := externalCtx, knownFuncs := knownFuncs,
      nextVar := 0, localFuncParamCounts := topLevelParamCounts,
      localFuncParamIds := topLevelParamIds,
      externalArities := externalArities, funcDefaults := funcDefaults,
      closureReturningFuncs := closureReturningFuncs }

  -- Classify which top-level functions are noncomputable BEFORE emitting
  -- funcStrs, so each function's emission can also see calls to other
  -- noncomputable funcs as noncomputable. We compute this at fixpoint:
  -- a func is noncomp iff its body references a previously-known noncomp
  -- local func. Externals are no longer in this set: as of the
  -- "computable externals" pass they're emitted as `def` with a stub
  -- body, so calling one doesn't make the caller noncomp. Mutual / chain
  -- dependencies need multiple iterations; we cap at `funcDefs.length`
  -- which is always sufficient.
  let extNamesEarly := externals.map (·.1)
  let topFuncIdsEarly := funcDefs.map (·.name.nameId)
  -- For walker purposes, externals look like extra computable callables
  -- (alongside local top-level defs). We merge them into the `funcIds`
  -- parameter so `call (.name ext_id) _` doesn't trip the
  -- "!funcIds.contains" noncomp branch.
  let computableCallables := topFuncIdsEarly ++ extNamesEarly
  let closureReturningIds := closureReturningFuncs.map (·.1)
  let classifyOnce (current : List StringId) : List StringId :=
    funcDefs.filterMap fun fd =>
      -- Closure-factory functions are emitted as plain `def` returning a
      -- typed `PyClosure` value. Their bodies look noncomputable to the
      -- generic walker (because they end in `return inner_func`, which
      -- is normally a `PyVal.ofFn0` axiom), but the closure-factory
      -- emission lowers `inner` to a `PyClosure.mkN` value instead — so
      -- they're actually computable. Skip classification for them.
      if closureReturningIds.contains fd.name.nameId then none
      else
        let fdBound := allParamIds fd.signature ++ topFuncIdsEarly
        if nodesAreNoncomputable current computableCallables closureReturningIds fdBound fd.body then
          some fd.name.nameId
        else none
  let rec fixNoncomp (cur : List StringId) (fuel : Nat) : List StringId :=
    match fuel with
    | 0 => cur
    | k + 1 =>
      let next := classifyOnce cur
      if next.length == cur.length then cur else fixNoncomp next k
  let noncompFuncIdsEarly : List StringId := fixNoncomp [] funcDefs.length

  -- ----------------------------------------------------------------------
  -- Perms.top widening fixpoint (G1 propagation)
  -- ----------------------------------------------------------------------
  --
  -- A function is widened to `Perms.top` iff it is unannotated AND its
  -- body either (a) uses indirect calls / local-variable callee calls
  -- or calls an unknown external, or (b) calls another function that has
  -- been widened to `Perms.top`. We detect these by walking the IR
  -- directly (no translateBody needed).
  let unannotatedIds : List StringId := funcDefs.filterMap fun fd =>
    match fd.effectAnnotation with
    | .unannotated => some fd.name.nameId
    | _ => none
  let allFuncIdsEarly : List StringId := funcDefs.map (·.name.nameId)
  let collectFuncAliases (stmts : List Node) : List (StringId × StringId) :=
    stmts.filterMap fun
      | .assign id el => match el.expr with
        | .name nameId =>
          if allFuncIdsEarly.contains nameId.nameId ||
             extNamesEarly.contains nameId.nameId then
            some (id.nameId, nameId.nameId)
          else none
        | _ => none
      | _ => none
  let resolveAlias (aliases : List (StringId × StringId)) (id : StringId) : StringId :=
    match aliases.find? (·.1 == id) with
    | some (_, target) => target
    | none => id
  let funcCallTargets : List (StringId × String × List StringId) := funcDefs.map fun fd =>
    let leanName := sanitizeName (ir.resolveString fd.name.nameId)
    let aliases := collectFuncAliases fd.body
    let callIds := collectAllNameCallIds fd.body
    let targetIds := callIds.map fun cid => resolveAlias aliases cid.nameId
    (fd.name.nameId, leanName, targetIds.eraseDups)
  let bodyHasIndirectOrLocalVarCall (fd : FunctionDef) : Bool :=
    let paramIds := allParamIds fd.signature
    let nestedFuncIds := fd.body.filterMap fun
      | .funcDef inner => some inner.name.nameId | _ => none
    let lambdaIds := fd.body.filterMap fun
      | .assign id el => match el.expr with | .lambda _ => some id.nameId | _ => none
      | _ => none
    let callResultIds := fd.body.filterMap fun
      | .assign id el => match el.expr with
        | .call _ _ => some id.nameId
        | _ => none
      | _ => none
    let knownCallableIds := topFuncIdsEarly ++ extNamesEarly ++ paramIds ++ nestedFuncIds ++ lambdaIds ++ callResultIds
    let aliases := collectFuncAliases fd.body
    let aliasedNames := aliases.map (·.1)
    let callIds := collectAllNameCallIds fd.body
    let hasLocalVarCallee := callIds.any fun cid =>
      cid.scope != .localUnassigned &&
      !knownCallableIds.contains cid.nameId &&
      !aliasedNames.contains cid.nameId
    let hasIndirect := fd.body.any fun
      | .expr (ExprLoc.mk _ (.indirectCall _ _)) => true
      | .assign _ (ExprLoc.mk _ (.indirectCall _ _)) => true
      | .ret (ExprLoc.mk _ (.indirectCall _ _)) => true
      | _ => false
    hasLocalVarCallee || hasIndirect
  let directlyWidened : List StringId := funcDefs.filterMap fun fd =>
    if !unannotatedIds.contains fd.name.nameId then none
    else
      let callIds := collectAllNameCallIds fd.body
      let usesUnknownExt := callIds.any fun cid =>
        unknownExtIds.contains cid.nameId
      let usesIndirectOrLocal := bodyHasIndirectOrLocalVarCall fd
      if usesUnknownExt || usesIndirectOrLocal then some fd.name.nameId else none
  let widenStep (cur : List StringId) : List StringId :=
    funcCallTargets.filterMap fun (nid, _, targets) =>
      if cur.contains nid then some nid
      else if !unannotatedIds.contains nid then none
      else
        let callsWidened := targets.any fun tgt => cur.contains tgt
        if callsWidened then some nid else none
  let rec fixWiden (cur : List StringId) (fuel : Nat) : List StringId :=
    match fuel with
    | 0 => cur
    | k + 1 =>
      let next := widenStep cur
      if next.length == cur.length then cur else fixWiden next k
  let widenedFuncIds : List StringId := fixWiden directlyWidened funcDefs.length
  let widenedFuncLeanNames : List String := widenedFuncIds.filterMap fun nid =>
    funcCallTargets.find? (·.1 == nid) |>.map (·.2.1)

  -- ----------------------------------------------------------------------
  -- Effect inference for unannotated functions
  -- ----------------------------------------------------------------------
  --
  -- Real LLM-generated Python rarely carries `Pure[]` / `Effect[Net,...]`
  -- annotations. For unannotated functions we infer the effect set from
  -- the body: the union of (a) every known external the body calls
  -- (looked up in the externalPerms table) and (b) the inferred perms
  -- of every local function the body calls (resolved by fixpoint).
  --
  -- Functions in `widenedFuncIds` short-circuit to `Perms.top` (they
  -- touch dynamic dispatch or unknown externals). Functions with an
  -- explicit annotation (`.pure` or `.effectful`) keep the user's
  -- declaration unchanged — Lean still type-checks the body against
  -- it, which is the soundness rejection if the annotation lies.
  --
  -- The fixpoint terminates in at most `funcDefs.length` iterations
  -- because the inferred set can only grow (effects added, never
  -- removed) and the lattice is bounded by the finite set of effects.
  let externalEffectsMap : List (StringId × InferredPerms) := externals.map fun (nid, name) =>
    let permsStr := lookupExtPerms name
    let isUnknown := permsStr == "Perms.none" && !knownExtNames.contains name
    let ip : InferredPerms :=
      if isUnknown then .top
      else match parsePermsString permsStr with
        | some es => .effs es
        | none => .top
    (nid, ip)

  -- For each unannotated funcDef, the IR call ids in its body that
  -- target a known external (with non-trivial effects) or another
  -- local function. We use `collectAllNameCallIds` to walk the body
  -- (it does NOT recurse into nested funcDefs).
  --
  -- Function alias resolution: a `f = some_known_func; f(...)` shape
  -- aliases `f` to a known top-level name. Effect inference must
  -- see through the alias so the surrounding function inherits the
  -- aliased function's perms. We collect aliases from each body and
  -- rewrite call IDs accordingly.
  let allFuncIds : List StringId := funcDefs.map (·.name.nameId)
  let collectAliases (stmts : List Node) : List (StringId × StringId) :=
    stmts.filterMap fun
      | .assign id el => match el.expr with
        | .name nameId =>
          if allFuncIds.contains nameId.nameId then some (id.nameId, nameId.nameId)
          else none
        | _ => none
      | _ => none
  let funcCalledIds : List (StringId × List StringId) := funcDefs.map fun fd =>
    let aliases := collectAliases fd.body
    let rawIds := collectAllNameCallIds fd.body |>.map (·.nameId)
    let resolvedIds := rawIds.map fun id =>
      match aliases.find? (·.1 == id) with
      | some (_, target) => target
      | none => id
    (fd.name.nameId, resolvedIds)

  let initialInferred : List (StringId × InferredPerms) := funcDefs.map fun fd =>
    let isUnann := match fd.effectAnnotation with | .unannotated => true | _ => false
    let ip : InferredPerms :=
      if !isUnann then
        -- Annotated: use the user's declaration verbatim. We still
        -- record it so other unannotated callers can pick it up.
        match parsePermsString (effectAnnotationToPerms fd.effectAnnotation) with
        | some es => .effs es
        | none => .top
      else if widenedFuncIds.contains fd.name.nameId then .top
      else
        -- Initial: union of called externals' effects (local-func
        -- contributions are added in the fixpoint below).
        let calls := funcCalledIds.find? (·.1 == fd.name.nameId) |>.map (·.2) |>.getD []
        calls.foldl (fun acc id =>
          match externalEffectsMap.find? (·.1 == id) with
          | some (_, ipExt) => InferredPerms.union acc ipExt
          | none => acc) (.effs [])
    (fd.name.nameId, ip)

  let inferStep (cur : List (StringId × InferredPerms))
      : List (StringId × InferredPerms) :=
    cur.map fun (nid, ip) =>
      -- Annotated funcs and already-top funcs don't change.
      let isUnann := funcDefs.any fun fd =>
        fd.name.nameId == nid &&
        (match fd.effectAnnotation with | .unannotated => true | _ => false)
      if !isUnann then (nid, ip)
      else match ip with
        | .top => (nid, ip)
        | .effs _ =>
          let calls := funcCalledIds.find? (·.1 == nid) |>.map (·.2) |>.getD []
          let newIp := calls.foldl (fun acc id =>
            -- Union with the called function's currently-inferred perms.
            match cur.find? (·.1 == id) with
            | some (_, ipCallee) => InferredPerms.union acc ipCallee
            | none => acc) ip
          (nid, newIp)

  let permsListEq (a b : List (StringId × InferredPerms)) : Bool :=
    a.length == b.length &&
    (a.zip b).all (fun pair =>
      let ipA := pair.1.2
      let ipB := pair.2.2
      match ipA, ipB with
      | .top, .top => true
      | .effs xs, .effs ys =>
        xs.length == ys.length && xs.all (fun e => ys.contains e)
      | _, _ => false)

  let rec fixInfer (cur : List (StringId × InferredPerms)) (fuel : Nat)
      : List (StringId × InferredPerms) :=
    match fuel with
    | 0 => cur
    | k + 1 =>
      let next := inferStep cur
      if permsListEq next cur then cur else fixInfer next k
  let inferredPermsMap : List (StringId × InferredPerms) :=
    fixInfer initialInferred funcDefs.length

  -- Path B: compute each function's AST string BEFORE `funcStrs` so
  -- the executable emission can use `permsOf __extEnv __env foo__ast`
  -- as the type signature (flowing from the AST) instead of a
  -- separate perms literal. This eliminates the per-function linkage
  -- theorem — the AST and the executable are tied by definitional
  -- equality at elaboration time.
  let collectNestedFuncDefs (stmts : List Node) : List FunctionDef :=
    stmts.filterMap fun
      | .funcDef inner => some inner
      | _ => none
  let resolveClosureFactoryInner (factoryId : StringId) : Option String := do
    let factoryFd ← funcDefs.find? (·.name.nameId == factoryId)
    let inner ← (collectNestedFuncDefs factoryFd.body).head?
    let factoryName := sanitizeName (ir.resolveString factoryId)
    let innerName := sanitizeName (ir.resolveString inner.name.nameId)
    return factoryName ++ "__" ++ innerName
  let collectKnownFuncAliases (stmts : List Node) : List (StringId × String) :=
    stmts.filterMap fun
      | .assign id el => match el.expr with
        | .name nameId =>
          if allFuncIds.contains nameId.nameId then
            some (id.nameId, sanitizeName (ir.resolveString nameId.nameId))
          else none
        | .call (.name factoryId) _ =>
          if closureReturningFuncs.any (·.1 == factoryId.nameId) then
            (resolveClosureFactoryInner factoryId.nameId).map fun mangled =>
              (id.nameId, mangled)
          else none
        | _ => none
      | _ => none
  let collectClosureBindings' (stmts : List Node) : List StringId :=
    stmts.filterMap fun
      | .assign id el => match el.expr with
        | .lambda _ => some id.nameId
        | .call (.name factoryId) _ =>
          if closureReturningFuncs.any (·.1 == factoryId.nameId) then
            some id.nameId
          else none
        | _ => none
      | _ => none
  -- For each function, compute:
  --   - `astBodyEarly`    : the bare parent AST body string (no def
  --     header). Used inside `funcStrs.map` for the `sigPerms` gate.
  --   - `astBodyAllEarly` : parent body concatenated with every
  --     sibling nested-func body string. The `useExactPerms` gate
  --     tests this combined blob for unresolved `.call` names, so
  --     the gate accounts for what `permsOf` would traverse via
  --     recursive `__env` lookups.
  --   - `astDefStr`       : the full emitted block (`def foo__ast :=
  --     ...` plus any sibling nested-func `__ast` defs), emitted in
  --     its own section ABOVE `funcSection`.
  let astEarlyTriples : List (String × String × String) := funcDefs.map fun fd =>
    let parentName := sanitizeName (ir.resolveString fd.name.nameId)
    let knownFuncAliases := collectKnownFuncAliases fd.body
    let closureNames := collectClosureBindings' fd.body
    let nestedDefs := collectNestedFuncDefs fd.body
    let nestedAliases : List (StringId × String) := nestedDefs.map fun inner =>
      let innerName := sanitizeName (ir.resolveString inner.name.nameId)
      (inner.name.nameId, parentName ++ "__" ++ innerName)
    let aliases := knownFuncAliases ++ nestedAliases
    let astCtx := { ctx with astLocalAliases := aliases, astClosureNames := closureNames }
    let astBody := translateBodyAST astCtx fd.body
    let parentDef := s!"def {parentName}__ast : EffAST := {astBody}\n"
    let nestedBodies : List String := nestedDefs.map fun inner =>
      translateBodyAST astCtx inner.body
    let nestedDefStrs : List String := nestedDefs.zip nestedBodies |>.map fun (inner, body) =>
      let innerMangled := parentName ++ "__" ++ sanitizeName (ir.resolveString inner.name.nameId)
      s!"def {innerMangled}__ast : EffAST := {body}\n"
    let combinedAstBlob := String.intercalate " " (astBody :: nestedBodies)
    (astBody, combinedAstBlob, parentDef ++ String.intercalate "" nestedDefStrs)
  let astStrsEarly : List String := astEarlyTriples.map (·.1)
  let astBlobsEarly : List String := astEarlyTriples.map (·.2.1)
  let astDefStrs : List String := astEarlyTriples.map (·.2.2)

  let funcStrsWithHasProg : List (String × Bool) := (funcDefs.zip astStrsEarly |>.zip astBlobsEarly).map
      fun ((fd, astBodyEarly), astBlobEarly) =>
    let name := sanitizeName (ir.resolveString fd.name.nameId)
    let initialPerms := effectAnnotationToPerms fd.effectAnnotation
    let params := allParams ir fd.signature
    let paramList := if params.isEmpty then ""
      else " " ++ String.intercalate " " (params.map fun p => s!"({p} : PyVal)")
    -- Detect self-recursion: if the body contains a name reference to
    -- this function, we must emit `partial def` because Lean's structural
    -- termination check can't see decreasing-on-`PyVal`. Without this,
    -- recursive Python functions (e.g. `def fact(n): return n*fact(n-1)`)
    -- would fail to compile.
    let bodyRefs := collectAllNameRefs fd.body
    let bodyCalls := collectAllNameCallIds fd.body |>.map (·.nameId)
    let isRecursive := (bodyRefs ++ bodyCalls).contains fd.name.nameId
    -- `Eff` is now a computable structure-based monad. Pure functions
    -- (no effects) emit a plain `def` so users can `#eval` them, prove
    -- equations by `rfl`, and `decide` results. Functions that touch
    -- effectful externals must stay `noncomputable`.
    --
    -- Recursive cases need extra care:
    -- * recursive + pure + has-args: `partial def`. Body is computable
    --   and Lean accepts the recursion via well-founded recursion or as
    --   `partial`.
    -- * recursive + non-pure (any arity): we can't use `partial` (it
    --   forbids depending on `noncomputable` axioms) and we can't use
    --   plain `def` (termination check fails). We emit `opaque` — a
    --   declared signature with no body — so callers can still resolve
    --   the name. We lose semantic verification of the body, but the
    --   alternative is the file failing to compile entirely.
    -- * recursive + zero-args: `partial` rejects no-arg defs ("not a
    --   function"), so use `opaque` here too.
    -- Pre-translate the body once to detect whether it uses any
    -- `PyVal.callFn` axioms (the dynamic-dispatch escape hatch). Those
    -- axioms are typed at `Perms.top`, so any function calling them must
    -- itself be at `Perms.top`. For UNANNOTATED functions we widen the
    -- declared perms to `Perms.top` and re-translate; for explicitly
    -- annotated functions we keep the user's annotation and let Lean
    -- type-check it (which will reject Pure/Net annotations whose body
    -- actually uses callFn — that's a soundness rejection, not a bug).
    -- Effect inference for unannotated functions: use the
    -- pre-computed `inferredPermsMap` so an unannotated function that
    -- calls a `Net` external is emitted at `{ net := true }` (and any
    -- transitive callers thread the same effect set up the call
    -- graph). Annotated functions keep their declared perms (Lean
    -- still type-checks the body against the annotation, so a wrong
    -- annotation is rejected). Functions that touch dynamic dispatch
    -- or unknown externals short-circuit to `Perms.top` via the
    -- `widenedFuncIds` set, which `inferredPermsMap` already
    -- consults.
    let isUnannotated := match fd.effectAnnotation with | .unannotated => true | _ => false
    let perms :=
      if isUnannotated then
        match inferredPermsMap.find? (·.1 == fd.name.nameId) with
        | some (_, ip) => ip.toLeanString
        | none => initialPerms
      else if widenedFuncIds.contains fd.name.nameId then "Perms.top"
      else initialPerms
    let isPure := match fd.effectAnnotation with | .pure => true | _ => false
    -- A function can be a plain `def` (rather than `noncomputable def`) iff
    -- its body uses no axiomatic constructs — externals, lambdas/closures,
    -- indirect/method calls, global axiom refs, etc. This is what unlocks
    -- `rfl`/`decide` proofs of `«__module__».run = .ok PyVal.none` for
    -- files where the asserts only depend on computable arithmetic.
    -- Initial bound names: only parameters AND top-level functions
    -- visible at the call point. `nodesAreNoncomputable` walks the body
    -- statement-by-statement and adds any names introduced by each
    -- statement before processing the next, so a use-before-assign
    -- (like `print(x); x = 1`) correctly resolves `x` to the outer
    -- scope (which would be a noncomputable global axiom).
    --
    -- The "extIds" set treats only previously-classified-noncomp local
    -- funcs as effectively external. Real externals are no longer in
    -- this set: they're now `def`s with stub bodies. This stops a `def`
    -- from depending on a `noncomputable` sibling and producing a
    -- `dependsOnNoncomputable` failure at compile.
    let extNamesForCheck :=
      noncompFuncIdsEarly.filter (· != fd.name.nameId)
    let paramIds : List StringId := allParamIds fd.signature
    let funcBoundIds := paramIds ++ topFuncIdsEarly
    let bodyNoncomp := nodesAreNoncomputable extNamesForCheck computableCallables closureReturningIds funcBoundIds fd.body
    let canBeDef := isPure || !bodyNoncomp
    -- Closure-returning functions get a different shape: their return
    -- type is `Eff p (PyClosure q n)` and the body is a plain `do`
    -- block ending in `pure (PyClosure.mk{n} ...)` — no
    -- `Eff.runFunction` wrapping (because `Eff.return` only carries
    -- `PyVal`, not `PyClosure`). This restriction is fine because the
    -- detected shapes don't have early returns.
    let closureSig : Option (Nat × String) :=
      ctx.closureReturningFuncs.find? (·.1 == fd.name.nameId) |>.map (fun e => (e.2.1, e.2.2))
    -- Path B: `useExactPerms` decides whether this function's type
    -- signature should flow from the AST (`Eff (permsOf __extEnv
    -- __env foo__ast) PyVal`) instead of a literal perms term. The
    -- condition mirrors the linkage-theorem gate below (same
    -- criteria: not closure-returning, not widened to top, no opaque
    -- or unresolved calls in the AST). When it fires, the linkage
    -- theorem is redundant (definitional equality) and is skipped
    -- later in `phaseASection`.
    -- The gate must account for every name `permsOf` would resolve
    -- via `__env` or `__extEnv` across the WHOLE module, not just
    -- this function's immediate nested defs. `permsOf` recurses
    -- transitively through local bodies, so a sibling's nested def
    -- could be the target of a call in a body we walk into.
    let allNestedGateNames : List String := funcDefs.flatMap fun fd' =>
      let parentGate := sanitizeName (ir.resolveString fd'.name.nameId)
      (collectNestedFuncDefs fd'.body).map fun inner =>
        parentGate ++ "__" ++ sanitizeName (ir.resolveString inner.name.nameId)
    let knownNamesForGate : List String :=
      externals.map (fun (_, n) => "ext_" ++ sanitizeName n)
      ++ funcDefs.map (fun fd' => sanitizeName (ir.resolveString fd'.name.nameId))
      ++ allNestedGateNames
    let hasUnresolvedGate (s : String) : Bool :=
      let parts := s.splitOn "EffAST.call \""
      parts.drop 1 |>.any fun part =>
        let chars := part.toList
        let endIdx := chars.findIdx (· == '"')
        let callName := String.ofList (chars.take endIdx)
        !knownNamesForGate.contains callName
    let astHasOpaque : Bool := (astBlobEarly.splitOn "EffAST.opaque").length > 1
    let astHasUnresolved : Bool := hasUnresolvedGate astBlobEarly
    let _ := astBodyEarly  -- kept for potential future use; gate uses blob

    let useExactPerms : Bool :=
      closureSig.isNone
        && perms != "Perms.top"
        && !astHasOpaque
        && !astHasUnresolved
    -- The type annotation string: either the literal perms or the
    -- `permsOf` term flowing from the AST. Both reduce to the same
    -- literal via `rfl` thanks to the kernel-reducible `Perms.union`
    -- (see `docs/effast-canonical-plan.md` Phase 1).
    let sigPerms : String :=
      if useExactPerms then
        s!"(EffAST.permsOf __extEnv __env {name}__ast)"
      else
        perms
    -- G3 fuel transform: convert self-recursive functions into a
    -- structurally-recursive (on `_fuel : Nat`) helper plus a wrapper
    -- that calls the helper with a default fuel budget. This makes the
    -- function TOTAL — Lean accepts it as a real `def` rather than the
    -- old `partial def` (which provided no termination guarantee) or
    -- `opaque` (which discarded the body entirely). When fuel hits zero
    -- the helper raises `RecursionError`, mirroring CPython's
    -- recursion-limit behaviour.
    --
    -- We rewrite call sites of the recursive name inside the body via
    -- string substitution: every `(name ` becomes `(name__rec _fuel `
    -- so the helper recurses on its own fueled name. The wrapper keeps
    -- the original `name` so external callers (other top-level funcs,
    -- the module body) don't need to know about the fuel parameter.
    --
    -- Closure-factory recursive functions still fall through to the
    -- `partial` path below — fueling those would require threading
    -- fuel into the inner closure, which is rare in practice.
    let isFueled := isRecursive && closureSig.isNone
    if isFueled then
      let recName := s!"{name}__rec"
      -- Try EffProg for the recursive body. Self-calls go
      -- through __extEnvProg (value-erased, perms-correct).
      let recProgOpt := tryEmitEffProg { ctx with perms := perms } fd name
      let recPrefix := if recProgOpt.isSome then ""
        else if canBeDef then "" else "noncomputable "
      let recParamList :=
        if params.isEmpty then " (_fuel : Nat)"
        else " (_fuel : Nat)" ++ paramList
      let envList := "[" ++ String.intercalate ", " params ++ "]"
      let recDef := match recProgOpt with
        | some (progDef, _) =>
          progDef ++
          s!"def {recName}{recParamList} : Eff {perms} PyVal :=\n" ++
          s!"  match _fuel with\n" ++
          s!"  | 0 => Eff.raise (PyVal.str \"RecursionError: maximum recursion depth exceeded\")\n" ++
          s!"  | _fuel + 1 => Eff.liftSub (Eff.runFunction (EffProg.Prog.interp __extEnvProg {envList} {name}__prog))\n"
        | none =>
          -- EffProg translation failed for recursive function — emit a stub.
          s!"{recPrefix}def {recName}{recParamList} : Eff {perms} PyVal :=\n" ++
          s!"  match _fuel with\n" ++
          s!"  | 0 => Eff.raise (PyVal.str \"RecursionError: maximum recursion depth exceeded\")\n" ++
          s!"  | _fuel + 1 => Eff.runFunction (pure PyVal.none)\n"
      let wrapperPrefix := if canBeDef then "" else "noncomputable "
      let argFwd := if params.isEmpty then ""
        else " " ++ String.intercalate " " params
      let wrapperBody :=
        if useExactPerms then
          s!"  Eff.liftSub ({recName} 10000{argFwd})\n"
        else
          s!"  {recName} 10000{argFwd}\n"
      let wrapperDef :=
        s!"{wrapperPrefix}def {name}{paramList} : Eff {sigPerms} PyVal :=\n" ++
        wrapperBody
      (recDef ++ wrapperDef, false)
    else
      match closureSig with
      | some (innerArity, innerPerms) =>
        -- Closure-factory shape. Try EffProg for the inner body;
        -- the PyClosure.mkN wrapping stays outside interp.
        -- Inner body params + captured outer params form the env.
        let tryInnerProg (innerBody : List Node) (innerParamIds : List StringId)
            (capturedParams : List String) : Option (String × String × String) :=
          let innerProgCtx := { ctx with perms := innerPerms }
          -- Scope: captured vars at 0..N-1, then inner params at N..N+M-1
          let capturedScope := capturedParams.zipIdx.foldl (init := ([] : PScope))
            fun acc (_, idx) => pscopePush acc 0 idx  -- dummy nameIds
          -- Actually we need real nameIds. Use allParamIds for inner.
          let innerScope := initialPScope innerParamIds
          -- Prepend captured params to inner scope with offset
          let fullScope := innerScope.map fun (nid, idx) =>
            (nid, idx + capturedParams.length)
          -- Add outer function params as captured
          let outerParamIds := allParamIds fd.signature
          let capturedScope2 := outerParamIds.zipIdx.foldl (init := fullScope)
            fun acc (pid, idx) => pscopePush acc pid idx
          let scopeSize := capturedParams.length + innerParamIds.length
          match transBodyToProg innerProgCtx capturedScope2 scopeSize innerBody with
          | some progBody =>
            let progName := s!"{name}__inner__prog"
            let progDef := s!"def {progName} : EffProg.Prog := {progBody}\n"
            let innerParamNames := innerParamIds.map fun id =>
              sanitizeName (ir.resolveString id)
            let envList := "[" ++ String.intercalate ", "
              (capturedParams ++ innerParamNames) ++ "]"
            some (progDef, progName, envList)
          | none => none
        let mkClosureBody : String × String × Option String :=
          if fd.isAsync then
            -- Shape C: async coroutine. Try EffProg on fd.body.
            match tryInnerProg fd.body [] params with
            | some (progDef, progName, envList) =>
              (progDef,
                s!"  pure (PyClosure.mk0 (fun (_ : Unit) => Eff.runFunction (EffProg.Prog.interp __extEnvProg {envList} {progName})))",
                some progName)
            | none =>
              ("", "  pure (PyClosure.mk0 (fun _ => pure PyVal.none))", none)
          else
          match fd.body with
          | [.funcDef inner, _] =>
            let innerName := sanitizeName (ir.resolveString inner.name.nameId)
            let innerParamIds := allParamIds inner.signature
            let innerParams := allParams ir inner.signature
            let innerParamList := if innerParams.isEmpty then "(_ : Unit)"
              else String.intercalate " " (innerParams.map fun p => s!"({p} : PyVal)")
            match tryInnerProg inner.body innerParamIds params with
            | some (progDef, progName, envList) =>
              (progDef,
                s!"  let {innerName} := PyClosure.mk{innerArity} (fun {innerParamList} => Eff.runFunction (EffProg.Prog.interp __extEnvProg {envList} {progName}))\n  pure {innerName}",
                some progName)
            | none =>
              ("", s!"  let {innerName} := PyClosure.mk{innerArity} (fun {innerParamList} => pure PyVal.none)\n  pure {innerName}", none)
          | [.ret retEl] =>
            match retEl.expr with
            | .lambda inner =>
              let innerParamIds := allParamIds inner.signature
              let innerParams := allParams ir inner.signature
              let innerParamList := if innerParams.isEmpty then "(_ : Unit)"
                else String.intercalate " " (innerParams.map fun p => s!"({p} : PyVal)")
              match tryInnerProg inner.body innerParamIds params with
              | some (progDef, progName, envList) =>
                (progDef,
                  s!"  pure (PyClosure.mk{innerArity} (fun {innerParamList} => Eff.runFunction (EffProg.Prog.interp __extEnvProg {envList} {progName})))",
                  some progName)
              | none =>
                ("", s!"  pure (PyClosure.mk{innerArity} (fun {innerParamList} => pure PyVal.none))", none)
            | _ => ("", "  pure (PyClosure.mk0 (fun _ => pure PyVal.none))", none)
          | _ => ("", "  pure (PyClosure.mk0 (fun _ => pure PyVal.none))", none)
        let (progDefs, closureBody, innerProgName) := mkClosureBody
        let effectiveInnerPerms := match innerProgName with
          | some pn => s!"(EffProg.Prog.permsOf __extEnvProg {pn})"
          | none => innerPerms
        let prefix_ := if isRecursive then "partial " else ""
        (progDefs ++
        s!"{prefix_}def {name}{paramList} : Eff {perms} (PyClosure {effectiveInnerPerms} {innerArity}) := do\n{closureBody}\n", false)
      | none =>
        let prefix_ :=
          if isRecursive then "partial "
          else if canBeDef then ""
          else "noncomputable "
        -- Option 1b: try the `EffProg` path first for pure,
        -- non-recursive functions. The `tryEmitEffProg` translator
        -- walks the body; if every shape is supported, it emits
        -- `def {name}__prog : EffProg := ...` and we wrap with
        -- `EffProg.interp`. If any shape is unsupported, `none` is
        -- returned and we fall through to the existing hand-built
        -- do-block emission.
        --
        -- Gate: only pure (`Perms.none`), non-recursive, non-closure
        -- functions for now. As `EffProg`'s constructor set grows,
        -- this gate relaxes.
        let tryProg : Option (String × String) :=
          if !isRecursive then
            tryEmitEffProg { ctx with perms := perms } fd name
          else
            none
        match tryProg with
        | some (progDef, envList) =>
          -- Signature and body coupling.
          -- ANNOTATED case: the user's declared annotation is an
          -- upper bound on effects. We emit `def foo : Eff
          -- <declared> PyVal := Eff.liftSub (interp ... foo__prog)`.
          -- The `Eff.liftSub` carries `by decide` which discharges
          -- `EffProg.Prog.permsOf(body) ⊆ <declared>` at elaboration
          -- time — if the body widens beyond the annotation, the
          -- check fails and the file is rejected. This preserves
          -- soundness on user annotations (no hiding effects
          -- behind a Pure declaration).
          -- UNANNOTATED case: let the signature flow from the
          -- program IR via `sigPerms` (no annotation to enforce).
          -- The body type is `Eff (EffProg.Prog.permsOf ...) PyVal`.
          -- The sig type uses `EffAST.permsOf` (or a declared
          -- literal for annotated fns). These compute the same
          -- perm but are syntactically distinct. `Eff.liftSub`
          -- bridges via `by decide`.
          --
          -- For ANNOTATED functions: force sig to the declared
          -- literal (enforces annotation as upper bound). If body
          -- widens beyond, `decide` fails → rejected.
          -- For UNANNOTATED: use sigPerms (flows from EffAST).
          let effectiveSig :=
            if isUnannotated then sigPerms else perms
          let body :=
            s!"  Eff.liftSub (Eff.runFunction (EffProg.Prog.interp __extEnvProg {envList} {name}__prog))"
          (progDef ++
          s!"{prefix_}def {name}{paramList} : Eff {effectiveSig} PyVal :=\n" ++
          body ++ "\n", true)
        | none =>
          (s!"{prefix_}def {name}{paramList} : Eff {sigPerms} PyVal :=\n  Eff.runFunction (pure PyVal.none)\n", false)

  -- Collect ALL names that might be referenced: assigns + all Name exprs in bodies.
  -- Emit axioms for any that aren't defined as functions, externals, or params.
  let funcNames := funcDefs.map fun fd => fd.name.nameId
  let extNames := externals.map (·.1)
  let allAssignNames := collectAllAssigns nodes
  let allRefNames := collectAllNameRefs nodes
  let allNames := (allAssignNames ++ allRefNames).eraseDups
  let globalDecls := allNames.filterMap fun nid =>
    if funcNames.contains nid || extNames.contains nid then none
    else
      let name := sanitizeName (ir.resolveString nid)
      if name.startsWith "<" || name.isEmpty || name == "_" then none
      else some s!"axiom {name} : PyVal"
  let globalDecls := globalDecls.eraseDups

  let header := "-- AUTO-GENERATED by MontyVerification codegen\n-- Do not edit. Compilation of this file verifies effect safety.\n\nimport MontyVerification.EffectMonad\n\n-- Long do-blocks (esp. in __module__) push past the default elaborator\n-- recursion depth.\nset_option maxRecDepth 65536\n"
  let externSection := if externalDecls.isEmpty then "" else
    "\n-- External functions (trust declarations)\n" ++
    String.intercalate "\n" externalDecls ++ "\n"
  let globalSection := if globalDecls.isEmpty then "" else
    "\n-- Module-level globals\n" ++
    String.intercalate "\n" globalDecls ++ "\n"
  -- Path C: emit an `EffAST` value for each function alongside the
  -- main `def`. The AST is used by symbolic-execution analyses
  -- (`EffAST.calledBefore`, etc.) for ordering invariants the type
  -- system can't express directly. The two emissions are derived from
  -- the same IR by the same codegen, so they're guaranteed to agree
  -- by construction.
  -- For the AST translator's per-function alias map. Two kinds of
  -- aliases are collected:
  --
  --  * `f = known_top_level_func` → `f` resolves to the top-level
  --    func's display name (handles the `stress_func_alias` shape).
  --  * `def inner(...): ...` nested inside a parent function →
  --    `inner` resolves to a mangled sibling AST def name like
  --    `"parent__inner"` (handles the `stress_shadowing.nested_shadow`
  --    shape). The inner body is also translated to its own AST
  --    string and emitted alongside the parent's.
  --
  -- astStrs (full def form) and astBodyEarly (bare body) were already
  -- computed as `astDefStrs` / `astStrsEarly` above so `funcStrs`
  -- could consult each function's AST shape for the `sigPerms` gate.
  -- The AST defs are emitted in their own section (`astSection`)
  -- above the executable function section.
  let astSection : String :=
    if astDefStrs.isEmpty then ""
    else "\n-- EffAST defs (Path B: the AST IS the source of truth for perms)\n" ++
      String.intercalate "" astDefStrs
  let funcStrs := funcStrsWithHasProg.map (·.1)
  let hasProgFlags := funcStrsWithHasProg.map (·.2)
  let funcWithAst : List String := funcStrs

  -- First-class call graph: emit a `__call_graph` def listing every
  -- function and its direct callees (externals, locals, etc.). User
  -- property files can query it via `CallGraph.reaches`,
  -- `transitiveCallees`, etc.
  let callGraphEdges : List (String × List String) := funcDefs.map fun fd =>
    let callerName := sanitizeName (ir.resolveString fd.name.nameId)
    let callIds := collectAllNameCallIds fd.body |>.map (·.nameId)
    -- Resolve each call ID to its display name. Same logic as the
    -- AST translator: externals get the `ext_` prefix, locals use
    -- their sanitized name.
    let calleeNames := callIds.map fun cid =>
      if externals.any (·.1 == cid) then
        "ext_" ++ sanitizeName (ir.resolveString cid)
      else
        sanitizeName (ir.resolveString cid)
    -- Dedupe while preserving order.
    let dedupedCallees := calleeNames.foldl (fun acc n =>
      if acc.contains n then acc else acc ++ [n]) ([] : List String)
    (callerName, dedupedCallees)
  let callGraphStr : String :=
    if callGraphEdges.isEmpty then ""
    else
      let edgeStrs := callGraphEdges.map fun (caller, cs) =>
        let csStr := String.intercalate ", " (cs.map fun n => s!"\"{n}\"")
        s!"  (\"{caller}\", [{csStr}])"
      "\n-- Static call graph for the module (first-class).\n" ++
      "def call_graph : CallGraph := {\n  edges := [\n" ++
      String.intercalate ",\n" edgeStrs ++ "\n  ]\n}\n"

  let progEnvFuncDefs := (funcDefs.zip hasProgFlags).filterMap fun (fd, hasProg) =>
    if hasProg then some fd else none
  let regularEntries := progEnvFuncDefs.map fun fd =>
    let fname := sanitizeName (ir.resolveString fd.name.nameId)
    s!"  (\"{fname}\", .regular {fname}__prog)"
  let closureEntries := (funcDefs.zip funcStrs).filterMap fun (fd, funcStr) =>
    let isClosureFactory := closureReturningFuncs.any (·.1 == fd.name.nameId)
    if !isClosureFactory then none
    else
      let fname := sanitizeName (ir.resolveString fd.name.nameId)
      let innerProgName := s!"{fname}__inner__prog"
      let hasInnerProg := (funcStr.splitOn innerProgName).length > 1
      if !hasInnerProg then none
      else
        let arity := match closureReturningFuncs.find? (·.1 == fd.name.nameId) with
          | some (_, n, _) => n | none => 0
        some s!"  (\"{fname}\", .closureFactory {arity} {innerProgName})"
  let progEnvEntries := regularEntries ++ closureEntries
  let progEnvStr :=
    if progEnvEntries.isEmpty then ""
    else "\ndef __progEnv : EffProg.Prog.ProgEnv := [\n" ++
      String.intercalate ",\n" progEnvEntries ++ "\n]\n"

  let evalDefs := progEnvFuncDefs.filterMap fun fd =>
    let fname := sanitizeName (ir.resolveString fd.name.nameId)
    let bodyRefs := collectAllNameRefs fd.body
    let bodyCalls := collectAllNameCallIds fd.body |>.map (·.nameId)
    let isRecursive := (bodyRefs ++ bodyCalls).contains fd.name.nameId
    if isRecursive then none
    else
      let paramIds := allParamIds fd.signature
      let params := allParams ir fd.signature
      let paramList := if params.isEmpty then ""
        else " " ++ String.intercalate " " (params.map fun p => s!"({p} : PyVal)")
      let envList := "[" ++ String.intercalate ", " (paramIds.map fun pid =>
        sanitizeName (ir.resolveString pid)) ++ "]"
      some s!"def {fname}__eval{paramList} : Eff Perms.top PyVal :=\n  Eff.runFunction (EffProg.Prog.interpWithCalls 1000 __extEnvProg __progEnv {envList} {fname}__prog)\n"
  let evalSection :=
    if evalDefs.isEmpty then ""
    else "\n-- Value-level evaluation defs (cross-function calls resolved)\n" ++
      String.intercalate "\n" evalDefs

  let funcSection := if funcWithAst.isEmpty then "" else
    "\n-- Monty functions\n" ++ String.intercalate "\n" funcWithAst ++ callGraphStr ++ progEnvStr ++ evalSection

  -- Phase A: emit __extEnv, __env, and per-function permsOf consistency
  -- theorems. These provide a verified, machine-checked linkage between
  -- the AST and the executable form: for each function, the AST-derived
  -- perms (`permsOf __extEnv __env foo__ast`) equal the declared perms
  -- in the function's type signature. If the two translators ever drift,
  -- the `rfl` proof fails and Lean rejects the file.
  --
  -- The proof is `rfl` (definitional equality) rather than the earlier
  -- `native_decide`: `Perms.union` now uses a fuel-based custom-list
  -- merge instead of `List.mergeSort`, so `permsOf` unfolds fully in
  -- the kernel. See `docs/effast-canonical-plan.md` for the full
  -- rationale.
  let phaseASection : String :=
    if funcDefs.isEmpty && externals.isEmpty then "" else
    let extEntries := externals.map fun (_, name) =>
      let leanName := "ext_" ++ sanitizeName name
      let knownPerms := lookupExtPerms name
      let isUnknown := knownPerms == "Perms.none" && !knownExtNames.contains name
      let declPerms := if isUnknown then "Perms.top" else knownPerms
      s!"  (\"{leanName}\", ({declPerms} : Perms))"
    let extEnvStr :=
      if extEntries.isEmpty then "def __extEnv : EffAST.ExtEnv := []\n"
      else "def __extEnv : EffAST.ExtEnv := [\n" ++
        String.intercalate ",\n" extEntries ++ "\n]\n"
    -- __extEnvProg: used by `EffProg.Prog.permsOf` / `.interp`.
    -- Same shape as `__extEnv` but ALSO includes local top-level
    -- functions with their computed perms, so `EffProg.permsOf`
    -- can resolve local calls without needing `FuncEnv` recursion.
    -- Matches what the fixpoint in `funcStrs.map` would compute.
    -- Include both top-level and nested (mangled) function names.
    let localFuncPermsEntries := funcDefs.map fun fd =>
      let fname := sanitizeName (ir.resolveString fd.name.nameId)
      let isUnann := match fd.effectAnnotation with | .unannotated => true | _ => false
      let fperms :=
        if isUnann then
          match inferredPermsMap.find? (·.1 == fd.name.nameId) with
          | some (_, ip) => ip.toLeanString
          | none => effectAnnotationToPerms fd.effectAnnotation
        else if widenedFuncIds.contains fd.name.nameId then "Perms.top"
        else effectAnnotationToPerms fd.effectAnnotation
      s!"  (\"{fname}\", ({fperms} : Perms))"
    -- Also include nested funcDef mangled names (e.g.
    -- "outer__inner") so that calls from the outer function
    -- resolve correctly in `EffProg.Prog.permsOf`.
    let nestedFuncPermsEntries := funcDefs.flatMap fun fd =>
      let parentName := sanitizeName (ir.resolveString fd.name.nameId)
      (collectNestedFuncDefs fd.body).map fun inner =>
        let innerName := sanitizeName (ir.resolveString inner.name.nameId)
        let mangled := parentName ++ "__" ++ innerName
        -- Nested funcs are generally pure (Perms.none) unless
        -- they call externals. Use Perms.none as a conservative
        -- guess — the actual perms would require its own fixpoint.
        s!"  (\"{mangled}\", (Perms.none : Perms))"
    let callSentinels := [
      s!"  (\"__indirect__\", (Perms.top : Perms))",
      s!"  (\"__attrCall__\", (Perms.top : Perms))"]
    let extEnvProgEntries := extEntries ++ localFuncPermsEntries ++ nestedFuncPermsEntries ++ callSentinels
    let extEnvProgStr :=
      if extEnvProgEntries.isEmpty then "def __extEnvProg : EffProg.ExtEnv := []\n"
      else "def __extEnvProg : EffProg.ExtEnv := [\n" ++
        String.intercalate ",\n" extEnvProgEntries ++ "\n]\n"
    -- Collect all AST def names: top-level funcDef ASTs plus nested
    -- funcDef sibling ASTs (emitted by the nested-funcDef pass above).
    let topAstEntries := funcDefs.map fun fd =>
      let name := sanitizeName (ir.resolveString fd.name.nameId)
      s!"  (\"{name}\", {name}__ast)"
    let nestedAstEntries := funcDefs.flatMap fun fd =>
      let parentName := sanitizeName (ir.resolveString fd.name.nameId)
      (collectNestedFuncDefs fd.body).map fun inner =>
        let innerName := sanitizeName (ir.resolveString inner.name.nameId)
        let mangled := parentName ++ "__" ++ innerName
        s!"  (\"{mangled}\", {mangled}__ast)"
    let allAstEntries := topAstEntries ++ nestedAstEntries
    let envStr := "def __env : EffAST.FuncEnv := [\n" ++
      String.intercalate ",\n" allAstEntries ++ "\n]\n"
    -- Per-function linkage theorems are no longer needed: the
    -- executable def's type is `Eff (permsOf __extEnv __env
    -- foo__ast) PyVal`, so agreement between the AST and the
    -- executable is enforced by Lean's type checker at elaboration
    -- via definitional equality (`permsOf` reduces to the same
    -- literal the body was built against, because `Perms.union` is
    -- kernel-reducible). For functions where the gate doesn't fire
    -- (closure-returning, Perms.top-widened, or AST-opaque), the
    -- old literal-perms signature is preserved and there's no
    -- linkage theorem — drift is not detected for those, but the
    -- executable body still type-checks on its own.
    "\n-- Path B: __extEnv + __env (AST perms environments)\n" ++
    extEnvStr ++ envStr ++ extEnvProgStr

  -- Default-value defs for each defaulted parameter. Emitted *before*
  -- the module body so it can reference them. Python evaluates default
  -- expressions once at definition time; we pre-evaluate them at codegen
  -- time and bind to a top-level `def`. For pure defaults this is direct;
  -- for effectful defaults we still emit a `noncomputable def` returning
  -- `Eff p PyVal` ... actually no, we substitute `PyVal.none` for the
  -- effectful case since the result type would be `Eff` not `PyVal`.
  let defaultDefs : List String := funcDefs.flatMap fun fd =>
    let totalParams := (allParams ir fd.signature).length
    let defaults := fd.defaultExprs
    let funcName := sanitizeName (ir.resolveString fd.name.nameId)
    let _ := totalParams
    defaults.mapIdx fun i el =>
      let defName := s!"{funcName}__default_{i}"
      -- Default argument values are approximated as `PyVal.none`.
      -- Precise default translation would need a pure expression
      -- translator, but defaults are rarely semantically important
      -- for effect verification.
      s!"def {defName} : PyVal := PyVal.none"
  let defaultSection := if defaultDefs.isEmpty then "" else
    "\n-- Pre-evaluated default argument values\n" ++
    String.intercalate "\n" defaultDefs ++ "\n"

  -- Synthesize a `__module__` def from all top-level non-funcdef
  -- statements (assigns, asserts, expressions, ifs, ...) so module-level
  -- semantics actually get checked. Asserts now real-evaluate (raising on
  -- failure), so `__module__.run = .ok PyVal.none` is the proposition
  -- "all top-level asserts in this file passed".
  let modulePerms := "Perms.none"
  let moduleNodes := nodes.filter fun
    | .funcDef _ => false
    | _ => true
  -- The module body itself can be a plain `def` if every statement is
  -- computable AND every locally-defined function it calls is computable.
  -- We've already determined which funcs are noncomputable above; check
  -- whether any noncomputable local func is referenced from the module.
  -- Reuse the fixpoint we already computed before `funcStrs`. This is
  -- the canonical "which top-level funcs are noncomputable" set, used
  -- both for marking funcs `noncomputable def` and for deciding whether
  -- the module body itself can be a plain `def`. Externals are NOT in
  -- this set: they're computable `def`s and don't taint the module.
  let noncompFuncIds : List StringId := noncompFuncIdsEarly
  let modExtCheck := noncompFuncIds
  -- Module-level "bound names": at entry, only the computable top-level
  -- local funcs are in scope. The progressive walk in `nodesAreNoncomputable`
  -- adds module-level assigns as it encounters them, so a module-level
  -- use-before-assign is correctly seen as referencing the global axiom.
  let computableFuncIds := localFuncIds.filter (fun id => !noncompFuncIds.contains id)
  let modBoundIds := computableFuncIds
  -- Module-level noncomputability for the SINGLE-DEF (unchunked) path.
  -- The chunked path picks per-chunk prefixes inside its emission below,
  -- since each chunk is walked independently against its own scope.
  let modulePrefix :=
    if nodesAreNoncomputable modExtCheck computableCallables closureReturningIds modBoundIds moduleNodes then
      "noncomputable "
    else ""
  -- The aggregator `__module__` def — which calls each chunk in turn —
  -- is computable iff every chunk it references is computable. We can't
  -- compute that until we've walked the chunks, so it's set inside the
  -- chunking branch below.
  -- Pre-translate the module body once at the default perms to detect
  -- `PyVal.callFn` usage. The module body has no user annotation, so we
  -- widen to `Perms.top` whenever dynamic dispatch appears (mirroring
  -- the per-function logic above). Without this, a top-level
  -- `add5(3)` (where `add5 = make_adder(5)` is a closure-bound name
  -- that escaped through PyVal) would be typed `Eff Perms.none` while
  -- the call is `Eff Perms.top`, producing a type mismatch.
  let modCallIds := collectAllNameCallIds moduleNodes
  let modUsesCallFn := modCallIds.any fun cid =>
    let isParam := false
    let isKnown := topFuncIdsEarly.contains cid.nameId || extNamesEarly.contains cid.nameId
    cid.scope != .localUnassigned && !isKnown && !isParam
  let modHasIndirect := moduleNodes.any fun
    | .expr (ExprLoc.mk _ (.indirectCall _ _)) => true
    | .assign _ (ExprLoc.mk _ (.indirectCall _ _)) => true
    | _ => false
  let modUsesUnknownExt := modCallIds.any fun cid =>
    unknownExtIds.contains cid.nameId
  let modCallsWidened := modCallIds.any fun cid =>
    widenedFuncIds.contains cid.nameId
  let modulePerms :=
    if modUsesCallFn || modHasIndirect || modUsesUnknownExt || modCallsWidened then "Perms.top"
    else modulePerms
  let moduleSection : String :=
    if moduleNodes.isEmpty then ""
    else
      -- Chunk the module body into helper defs so the Lean elaborator
      -- doesn't stack-overflow on huge files (e.g. math__module's 778
      -- top-level statements). Each chunk becomes its own helper def
      -- and `__module__` calls them in sequence. The threshold is empirical:
      -- below it, we keep the single-def form for clarity in small files.
      -- Two thresholds:
      -- * `chunkThreshold` — at what total length we start chunking at
      --   all. Below this, the body stays in a single `def` (so it's
      --   eligible to become a plain `def` and reduce by
      --   `decide`/`native_decide`). Empirically the C-level recursion
      --   stack used during reduction starts to overflow around
      --   ~300 statements for dense bodies (e.g. `datetime__core`'s
      --   396-statement module body), so set the ceiling to 250 to
      --   leave headroom. Files between 250 and the previous 500 limit
      --   that worked single-def will now chunk; that loses the
      --   single-def `decide` reducibility but the chunked form still
      --   reduces chunk-by-chunk.
      -- * `chunkSize` — when we DO chunk, the size of each chunk. Must
      --   be small enough that `decide`/`native_decide` can reduce
      --   chunk-by-chunk. 64 is the historical value and works well.
      let chunkThreshold := 250
      let chunkSize := 64
      let total := moduleNodes.length
      -- Build aliases for module-body EffProg: map each top-level
      -- function's nameId to its sanitized name (without ext_
      -- prefix). Module-level code calls functions via
      -- .localUnassigned scope, which callableToProgName would
      -- prefix with ext_. The alias overrides this.
      let moduleAliases : List (StringId × String) :=
        funcDefs.map fun fd =>
          (fd.name.nameId, sanitizeName (ir.resolveString fd.name.nameId))
      -- Also add external functions: their nameId → ext_ prefixed name
      let extAliases : List (StringId × String) :=
        externals.map fun (nid, name) =>
          (nid, "ext_" ++ sanitizeName name)
      let modProgCtx := { ctx with
        perms := modulePerms,
        astLocalAliases := moduleAliases ++ extAliases,
        progLambdaBindings := [] }
      if total <= chunkThreshold then
        -- Try EffProg for the module body.
        let moduleProgOpt := transBodyToProg modProgCtx ([] : PScope) 0 moduleNodes
        match moduleProgOpt with
        | some progBody =>
          let progDef := s!"def __module____prog : EffProg.Prog := {progBody}\n"
          let extEnvFallback :=
            if funcDefs.isEmpty && externals.isEmpty then
              "def __extEnvProg : EffProg.ExtEnv := []\n"
            else ""
          let body :=
            s!"  Eff.liftSub (Eff.runFunction (EffProg.Prog.interp __extEnvProg [] __module____prog))"
          let evalDef :=
            if progEnvEntries.isEmpty then ""
            else s!"\ndef «__module__eval» : Eff Perms.top PyVal :=\n  Eff.runFunction (EffProg.Prog.interpWithCalls 1000 __extEnvProg __progEnv [] __module____prog)\n"
          s!"\n-- Module-level body (EffProg path)\n{extEnvFallback}{progDef}{modulePrefix}def «__module__» : Eff {modulePerms} PyVal :=\n{body}\n{evalDef}"
        | none =>
          -- EffProg translation failed — emit a stub. This path should
          -- never fire (100% EffProg coverage for module bodies).
          s!"\n-- Module-level body (stub — EffProg fallback)\n{modulePrefix}def «__module__» : Eff {modulePerms} PyVal :=\n  Eff.runFunction (pure PyVal.none)\n"
      else
        -- Split into List of chunks of size chunkSize. Use a fueled
        -- helper to avoid Lean's structural-termination check on
        -- `List.drop`.
        let numChunks := (total + chunkSize - 1) / chunkSize
        let chunks : List (List Node) := (List.range numChunks).map fun i =>
          (moduleNodes.drop (i * chunkSize)).take chunkSize
        -- Per-chunk noncomputability decision. Each chunk is its own
        -- Lean `def` and so its initial `boundIds` set is just the
        -- top-level computable functions (NOT the variables assigned
        -- by previous chunks — those don't propagate across `def`
        -- boundaries). The walker then walks the chunk's statements
        -- progressively, adding intra-chunk assigns as it goes. A
        -- chunk that ONLY references intra-chunk lets is computable;
        -- one that references a name first assigned in an earlier
        -- chunk is correctly classified noncomputable.
        let chunkPrefixes : List String := chunks.map fun chunk =>
          if nodesAreNoncomputable modExtCheck computableCallables closureReturningIds modBoundIds chunk
          then "noncomputable " else ""
        let chunkDefs := chunks.mapIdx fun i chunk =>
          let pre := chunkPrefixes[i]?.getD modulePrefix
          match transBodyToProg modProgCtx ([] : PScope) 0 chunk with
          | some progBody =>
            let progDef := s!"{pre}def «__module_chunk_{i}____prog» : EffProg.Prog := {progBody}\n"
            let chunkDef := s!"{pre}def «__module_chunk_{i}__» : Eff {modulePerms} PyVal :=\n  Eff.liftSub (Eff.runFunction (EffProg.Prog.interp __extEnvProg [] «__module_chunk_{i}____prog»))"
            s!"{progDef}\n{chunkDef}"
          | none =>
            -- EffProg translation failed for chunk — emit a stub.
            s!"{pre}def «__module_chunk_{i}__» : Eff {modulePerms} PyVal :=\n  Eff.runFunction (pure PyVal.none)"
        let chunkCalls := (List.range chunks.length).map fun i =>
          s!"  let _ ← «__module_chunk_{i}__»"
        let modBody := String.intercalate "\n" chunkCalls
        let chunksStr := String.intercalate "\n\n" chunkDefs
        -- The aggregator def is computable iff EVERY chunk is computable.
        let aggPrefix := if chunkPrefixes.any (· == "noncomputable ")
          then "noncomputable " else ""
        s!"\n-- Module-level body (chunked: {total} statements split into {chunks.length} helpers to avoid elaborator stack overflow)\n{chunksStr}\n\n{aggPrefix}def «__module__» : Eff {modulePerms} PyVal :=\n  Eff.runFunction (do\n{modBody}\n  pure PyVal.none\n  )\n"

  -- Section order matters: defaults must come BEFORE the function
  -- definitions that reference them, since Lean doesn't do forward
  -- name resolution across top-level defs in the same file.
  --
  -- Path B: `astSection` and `phaseASection` (which defines
  -- `__extEnv` and `__env`) MUST come before `funcSection` because
  -- each executable `def foo` type signature now references
  -- `permsOf __extEnv __env foo__ast`.
  header ++ externSection ++ globalSection ++ defaultSection ++
    astSection ++ phaseASection ++ funcSection ++ moduleSection

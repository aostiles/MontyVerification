import MontyVerification.Basic
import Lean.Data.Json

/-!
# JSON Deserialization for Monty IR

Parses the JSON output of `monty::emit_ir_json` into the Lean types defined
in `Basic.lean`. Uses `Lean.Json` (built-in).

## Serde JSON Format

Rust's serde serializes enums with the externally-tagged format:
- Unit variants → JSON string: `"Add"`, `"Local"`, `"Pure"`
- Newtype variants → `{"VariantName": inner_value}`
- Struct variants → `{"VariantName": {"field1": v1, "field2": v2}}`
- Tuple variants → `{"VariantName": [v1, v2]}`

Field names use `snake_case` in JSON (Rust convention).
-/

open Lean (Json ToJson FromJson)

-- ============================================================================
-- Error helpers
-- ============================================================================

/-- Parsing context for error messages. -/
abbrev ParseResult (α : Type) := Except String α

/-- Get a field from a JSON object. Returns `.null` if the key is missing or null. -/
private def field (obj : Json) (key : String) : ParseResult Json :=
  .ok (obj.getObjValD key)

private def fieldOpt (obj : Json) (key : String) : ParseResult (Option Json) :=
  match obj.getObjValD key with
  | .null => .ok none
  | v => .ok (some v)

private def asStr (j : Json) : ParseResult String :=
  match j with
  | .str s => .ok s
  | _ => .error s!"expected string, got {j}"

private def jsonNumToInt (n : Lean.JsonNumber) : Int :=
  -- For integer JSON values, exponent is 0 and mantissa is the value.
  -- For values with exponent > 0, multiply mantissa by 10^exponent.
  if n.exponent == 0 then n.mantissa
  else n.mantissa * (10 ^ n.exponent : Nat)

private def asNat (j : Json) : ParseResult Nat :=
  match j with
  | .num n => .ok (jsonNumToInt n).toNat
  | _ => .error s!"expected number, got {j}"

private def asInt (j : Json) : ParseResult Int :=
  match j with
  | .num n => .ok (jsonNumToInt n)
  | _ => .error s!"expected integer, got {j}"

private def asBool (j : Json) : ParseResult Bool :=
  match j with
  | .bool b => .ok b
  | _ => .error s!"expected bool, got {j}"

private def asFloat (j : Json) : ParseResult Float :=
  match j with
  | .num n => .ok n.toFloat
  | .str "Infinity" => .ok (1.0 / 0.0)
  | .str "-Infinity" => .ok (-1.0 / 0.0)
  | _ => .error s!"expected float, got {j}"

private def asArr (j : Json) : ParseResult (Array Json) :=
  match j with
  | .arr a => .ok a
  | _ => .error s!"expected array, got {j}"

/-- Parse a JSON array using a mapping function. -/
private def parseList (arr : Array Json) (f : Json → ParseResult α) : ParseResult (List α) :=
  arr.toList.mapM f

/-- Try to get the single key-value pair from a JSON object (serde externally-tagged enum). -/
private def taggedVariant (j : Json) : ParseResult (String × Json) :=
  match j with
  | .str s => .ok (s, .null)
  | .obj kvs =>
    match kvs.toArray with
    | #[⟨k, v⟩] => .ok (k, v)
    | _ => .error s!"expected single-key object for tagged enum, got {j}"
  | _ => .error s!"expected string or object for tagged enum, got {j}"

-- ============================================================================
-- Base types
-- ============================================================================

private def parsePosition (j : Json) : ParseResult Position := do
  let line ← field j "line" >>= asNat
  let col ← field j "column" >>= asNat
  return ⟨line, col⟩

private def parseCodeRange (j : Json) : ParseResult CodeRange := do
  let filename ← field j "filename" >>= asNat
  let previewLine ← match ← fieldOpt j "preview_line" with
    | some v => asNat v
    | none => pure 0
  let start ← field j "start" >>= parsePosition
  let «end» ← field j "end" >>= parsePosition
  return ⟨filename, previewLine, start, «end»⟩

private def parseNameScope (j : Json) : ParseResult NameScope := do
  let s ← asStr j
  match s with
  | "Local" => return .local
  | "LocalUnassigned" => return .localUnassigned
  | "Global" => return .global
  | "Cell" => return .cell
  | _ => .error s!"unknown NameScope: {s}"

private def parseIdentifier (j : Json) : ParseResult Identifier := do
  let pos ← field j "position" >>= parseCodeRange
  let nameId ← field j "name_id" >>= asNat
  let optNs ← fieldOpt j "opt_namespace_id"
  let optNsId ← match optNs with
    | some v => pure (some (← asNat v))
    | none => pure none
  let scope ← field j "scope" >>= parseNameScope
  return ⟨pos, nameId, optNsId, scope⟩

private def parseOperator (j : Json) : ParseResult Operator := do
  let s ← asStr j
  match s with
  | "Add" => return .add
  | "Sub" => return .sub
  | "Mult" => return .mult
  | "MatMult" => return .matMult
  | "Div" => return .div
  | "Mod" => return .mod
  | "Pow" => return .pow
  | "LShift" => return .lShift
  | "RShift" => return .rShift
  | "BitOr" => return .bitOr
  | "BitXor" => return .bitXor
  | "BitAnd" => return .bitAnd
  | "FloorDiv" => return .floorDiv
  | "And" => return .and
  | "Or" => return .or
  | _ => .error s!"unknown Operator: {s}"

private def parseCmpOperator (j : Json) : ParseResult CmpOperator := do
  match j with
  | .str s =>
    match s with
    | "Eq" => return .eq
    | "NotEq" => return .notEq
    | "Lt" => return .lt
    | "LtE" => return .ltE
    | "Gt" => return .gt
    | "GtE" => return .gtE
    | "Is" => return .is
    | "IsNot" => return .isNot
    | "In" => return .in
    | "NotIn" => return .notIn
    | _ => .error s!"unknown CmpOperator: {s}"
  | .obj _ => do
    let (tag, val) ← taggedVariant j
    match tag with
    | "ModEq" => return .modEq (← asInt val)
    | _ => .error s!"unknown CmpOperator variant: {tag}"
  | _ => .error s!"expected string or object for CmpOperator, got {j}"

private def parseLiteral (j : Json) : ParseResult Literal := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "None" => return .none
  | "Ellipsis" => return .ellipsis
  | "Bool" => return .bool (← asBool val)
  | "Int" => return .int (← asInt val)
  | "Float" => return .float (← asFloat val)
  | "Str" => return .str (← asNat val)
  | "Bytes" => return .bytes (← asNat val)
  | "LongInt" => return .longInt (← asNat val)
  | "Marker" => return .marker 0  -- opaque, extract tag if needed
  | _ => .error s!"unknown Literal variant: {tag}"

-- ============================================================================
-- Effects
-- ============================================================================

private def parseEffect (j : Json) : ParseResult Effect := do
  match j with
  | .str s =>
    match s with
    | "FS" => return .fs
    | "Net" => return .net
    | "Env" => return .env
    | "Time" => return .time
    | _ => .error s!"unknown Effect: {s}"
  | .obj _ => do
    let (tag, val) ← taggedVariant j
    match tag with
    | "Custom" => return .custom (← asNat val)
    | _ => .error s!"unknown Effect variant: {tag}"
  | _ => .error s!"expected string or object for Effect, got {j}"

private def parseEffectAnnotation (j : Json) : ParseResult EffectAnnotation := do
  match j with
  | .str "Pure" => return .pure
  | .str "Unannotated" => return .unannotated
  | .str s => .error s!"unknown EffectAnnotation string: {s}"
  | .obj _ => do
    let (tag, val) ← taggedVariant j
    match tag with
    | "Effectful" => do
      let arr ← asArr val
      let effects ← parseList arr parseEffect
      return .effectful effects
    | _ => .error s!"unknown EffectAnnotation variant: {tag}"
  | _ => .error s!"expected string or object for EffectAnnotation, got {j}"

-- ============================================================================
-- Signature
-- ============================================================================

private def parseBindMode (j : Json) : ParseResult BindMode := do
  let s ← asStr j
  match s with
  | "Simple" | "SimpleWithDefaults" => return .simple
  | "Complex" => return .complexArgs
  | _ => .error s!"unknown BindMode: {s}"

private def parseOptStringIdList (j : Json) : ParseResult (Option (List StringId)) :=
  match j with
  | .null => .ok none
  | .arr a => do
    let ids ← parseList a asNat
    return some ids
  | _ => .error s!"expected null or array for optional StringId list"

private def parseOptKwargDefaultMap (j : Json) : ParseResult (Option (List (Option Nat))) :=
  match j with
  | .null => .ok none
  | .arr a => do
    let items ← parseList a fun item =>
      match item with
      | .null => return none
      | _ => return some (← asNat item)
    return some items
  | _ => .error s!"expected null or array for kwarg_default_map"

private def parseSignature (j : Json) : ParseResult Signature := do
  let posArgs ← field j "pos_args" >>= parseOptStringIdList
  let posDefaultsCount ← field j "pos_defaults_count" >>= asNat
  let args ← field j "args" >>= parseOptStringIdList
  let argDefaultsCount ← field j "arg_defaults_count" >>= asNat
  let varArgs ← match ← fieldOpt j "var_args" with
    | some v => pure (some (← asNat v))
    | none => pure none
  let kwargs ← field j "kwargs" >>= parseOptStringIdList
  let kwargDefaultMap ← field j "kwarg_default_map" >>= parseOptKwargDefaultMap
  let varKwargs ← match ← fieldOpt j "var_kwargs" with
    | some v => pure (some (← asNat v))
    | none => pure none
  let bindMode ← field j "bind_mode" >>= parseBindMode
  return ⟨posArgs, posDefaultsCount, args, argDefaultsCount, varArgs,
          kwargs, kwargDefaultMap, varKwargs, bindMode⟩

-- ============================================================================
-- Callable
-- ============================================================================

/-- Parse an `EitherStr` value from JSON. In Monty's IR, attribute names are
    either interned (`{"Interned": id}`) or heap strings (`{"Heap": str}`).
    We normalize both to a `StringId` (using 0 as fallback for heap strings). -/
private def parseEitherStr (j : Json) : ParseResult StringId := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Interned" => asNat val
  | "Heap" => return 0  -- fallback for non-interned strings
  | _ => .error s!"unknown EitherStr variant: {tag}"

/-- Extract the function/type name from a Monty IR `Builtin` payload.
    The IR shape is `{"Function": "Len"}` / `{"Type": "Str"}` /
    `{"ExcType": "TypeError"}`; we return the inner string. Returns the
    empty string if we can't recognise the shape (caller falls back to
    the legacy opaque path). -/
private def parseBuiltinName (val : Json) : String :=
  match val with
  | .obj o =>
    match o.toArray.toList with
    | [(_, .str s)] => s
    | _ => ""
  | _ => ""

private def parseCallable (j : Json) : ParseResult Callable := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Builtin" => return .builtin (parseBuiltinName val)
  | "Name" => return .name (← parseIdentifier val)
  | _ => .error s!"unknown Callable variant: {tag}"

-- ============================================================================
-- Mutually recursive parsers
-- ============================================================================

-- Forward declarations via mutual block.
-- The JSON for these types is deeply nested, so we use fuel-based recursion
-- to satisfy Lean's termination checker.

/-- Fuel-limited recursive parser. The fuel decreases with each recursive call,
    preventing infinite recursion from malformed JSON. 10000 is sufficient
    for any reasonable Python program's IR. -/
private def defaultFuel : Nat := 10000

mutual

private partial def parseExprLoc (fuel : Nat) (j : Json) : ParseResult ExprLoc :=
  match fuel with
  | 0 => .error "parse fuel exhausted"
  | fuel + 1 => do
    let pos ← field j "position" >>= parseCodeRange
    let exprJson ← field j "expr"
    let e ← parseExpr fuel exprJson
    return .mk pos e

private partial def parseExpr (fuel : Nat) (j : Json) : ParseResult Expr :=
  match fuel with
  | 0 => .error "parse fuel exhausted"
  | fuel + 1 => do
    let (tag, val) ← taggedVariant j
    match tag with
    | "Literal" => return .literal (← parseLiteral val)
    | "Builtin" => return .builtin (parseBuiltinName val)
    | "Name" => return .name (← parseIdentifier val)
    | "Call" => do
      let callable ← field val "callable" >>= parseCallable
      let args ← field val "args" >>= parseArgExprs fuel
      return .call callable args
    | "AttrCall" => do
      let obj ← field val "object" >>= parseExprLoc fuel
      let attr ← field val "attr" >>= parseEitherStr
      let args ← field val "args" >>= parseArgExprs fuel
      return .attrCall obj attr args
    | "IndirectCall" => do
      let callable ← field val "callable" >>= parseExprLoc fuel
      let args ← field val "args" >>= parseArgExprs fuel
      return .indirectCall callable args
    | "AttrGet" => do
      let obj ← field val "object" >>= parseExprLoc fuel
      let attr ← field val "attr" >>= parseEitherStr
      return .attrGet obj attr
    | "Op" => do
      let left ← field val "left" >>= parseExprLoc fuel
      let op ← field val "op" >>= parseOperator
      let right ← field val "right" >>= parseExprLoc fuel
      return .op left op right
    | "CmpOp" => do
      let left ← field val "left" >>= parseExprLoc fuel
      let op ← field val "op" >>= parseCmpOperator
      let right ← field val "right" >>= parseExprLoc fuel
      return .cmpOp left op right
    | "ChainCmp" => do
      let left ← field val "left" >>= parseExprLoc fuel
      let compsJson ← field val "comparisons" >>= asArr
      let comps ← parseList compsJson fun item => do
        let arr ← asArr item
        match arr.toList with
        | [opJ, exprJ] => return (← parseCmpOperator opJ, ← parseExprLoc fuel exprJ)
        | _ => .error "chain comparison pair must have 2 elements"
      return .chainCmp left comps
    | "List" => do
      let items ← asArr val >>= fun a => parseList a (parseSequenceItem fuel)
      return .list items
    | "Tuple" => do
      let items ← asArr val >>= fun a => parseList a (parseSequenceItem fuel)
      return .tuple items
    | "Dict" => do
      let items ← asArr val >>= fun a => parseList a (parseDictItem fuel)
      return .dict items
    | "Set" => do
      let items ← asArr val >>= fun a => parseList a (parseSequenceItem fuel)
      return .set items
    | "Subscript" => do
      let obj ← field val "object" >>= parseExprLoc fuel
      let idx ← field val "index" >>= parseExprLoc fuel
      return .subscript obj idx
    | "Slice" => do
      let lower ← parseOptExprLoc fuel val "lower"
      let upper ← parseOptExprLoc fuel val "upper"
      let step ← parseOptExprLoc fuel val "step"
      return .slice lower upper step
    | "Not" => return .not (← parseExprLoc fuel val)
    | "UnaryMinus" => return .unaryMinus (← parseExprLoc fuel val)
    | "UnaryPlus" => return .unaryPlus (← parseExprLoc fuel val)
    | "UnaryInvert" => return .unaryInvert (← parseExprLoc fuel val)
    | "Await" => return .await (← parseExprLoc fuel val)
    | "FString" => do
      let parts ← asArr val >>= fun a => parseList a (parseFStringPart fuel)
      return .fstring parts
    | "IfElse" => do
      let test ← field val "test" >>= parseExprLoc fuel
      let body ← field val "body" >>= parseExprLoc fuel
      let orelse ← field val "orelse" >>= parseExprLoc fuel
      return .ifElse test body orelse
    | "ListComp" => do
      let elt ← field val "elt" >>= parseExprLoc fuel
      let gens ← field val "generators" >>= asArr >>= fun a =>
        parseList a (parseComprehension fuel)
      return .listComp elt gens
    | "SetComp" => do
      let elt ← field val "elt" >>= parseExprLoc fuel
      let gens ← field val "generators" >>= asArr >>= fun a =>
        parseList a (parseComprehension fuel)
      return .setComp elt gens
    | "DictComp" => do
      let key ← field val "key" >>= parseExprLoc fuel
      let value ← field val "value" >>= parseExprLoc fuel
      let gens ← field val "generators" >>= asArr >>= fun a =>
        parseList a (parseComprehension fuel)
      return .dictComp key value gens
    | "Lambda" => do
      let funcDef ← field val "func_def" >>= parseFunctionDef fuel
      return .lambda funcDef
    | "Named" => do
      let target ← field val "target" >>= parseIdentifier
      let value ← field val "value" >>= parseExprLoc fuel
      return .named target value
    | "LambdaRaw" =>
      -- Should not appear in prepared IR, but handle gracefully
      .error "LambdaRaw should not appear in prepared IR"
    | _ => .error s!"unknown Expr variant: {tag}"

private partial def parseOptExprLoc (fuel : Nat) (obj : Json) (key : String) : ParseResult (Option ExprLoc) := do
  match ← fieldOpt obj key with
  | some v => return some (← parseExprLoc fuel v)
  | none => return none

private partial def parseSequenceItem (fuel : Nat) (j : Json) : ParseResult SequenceItem := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Value" => return .value (← parseExprLoc fuel val)
  | "Unpack" => return .unpack (← parseExprLoc fuel val)
  | _ => .error s!"unknown SequenceItem variant: {tag}"

private partial def parseDictItem (fuel : Nat) (j : Json) : ParseResult DictItem := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Pair" => do
    let arr ← asArr val
    match arr.toList with
    | [k, v] => return .pair (← parseExprLoc fuel k) (← parseExprLoc fuel v)
    | _ => .error "DictItem::Pair must have exactly 2 elements"
  | "Unpack" => return .unpack (← parseExprLoc fuel val)
  | _ => .error s!"unknown DictItem variant: {tag}"

private partial def parseComprehension (fuel : Nat) (j : Json) : ParseResult Comprehension := do
  let target ← field j "target" >>= parseUnpackTarget fuel
  let iter ← field j "iter" >>= parseExprLoc fuel
  let ifsArr ← field j "ifs" >>= asArr
  let ifs ← parseList ifsArr (parseExprLoc fuel)
  return .mk target iter ifs

private partial def parseFStringFormatSpec (fuel : Nat) (j : Json) : ParseResult FStringFormatSpec := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Static" => return .literal 0  -- opaque parsed format spec
  | "Dynamic" => do
    -- Dynamic format spec contains nested FStringParts; we approximate
    -- by parsing the first part's expression if available
    let arr ← asArr val
    match arr.toList with
    | first :: _ => do
      let part ← parseFStringPart fuel first
      match part with
      | .value expr _ _ => return .dynamic expr
      | .literal _ => return .literal 0
    | _ => return .literal 0
  | _ => .error s!"unknown FStringFormatSpec variant: {tag}"

private partial def parseFStringPart (fuel : Nat) (j : Json) : ParseResult FStringPart := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Literal" => return .literal (← asNat val)
  | "Interpolation" => do
    let expr ← field val "expr" >>= parseExprLoc fuel
    -- conversion is a ConversionFlag enum (None/Str/Repr/Ascii), map to optional Nat
    let conv ← match (← field val "conversion") with
      | .str "None" => pure none
      | .str "Str" => pure (some 1)
      | .str "Repr" => pure (some 2)
      | .str "Ascii" => pure (some 3)
      | _ => pure none
    let fmtSpec ← match ← fieldOpt val "format_spec" with
      | some v => pure (some (← parseFStringFormatSpec fuel v))
      | none => pure none
    return .value expr conv fmtSpec
  | _ => .error s!"unknown FStringPart variant: {tag}"

private partial def parseArgExprs (fuel : Nat) (j : Json) : ParseResult ArgExprs := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Empty" => return .simple []
  | "One" => do
    let expr ← parseExprLoc fuel val
    return .simple [expr]
  | "Two" => do
    let arr ← asArr val
    match arr.toList with
    | [a, b] => return .simple [← parseExprLoc fuel a, ← parseExprLoc fuel b]
    | _ => .error "ArgExprs::Two must have exactly 2 elements"
  | "Args" => do
    let arr ← asArr val
    let exprs ← parseList arr (parseExprLoc fuel)
    return .simple exprs
  | "Kwargs" => do
    -- `Kwargs` is a list of named keyword arguments, e.g. `f(x=1, y=2)`.
    -- Each entry has a `key` (Identifier) and `value` (ExprLoc). We
    -- preserve them as a `.generalizedCall` so call sites can do
    -- name-based parameter binding.
    let arr ← asArr val
    let kwargsList ← arr.toList.mapM fun kw => do
      let key ← field kw "key" >>= parseIdentifier
      let value ← field kw "value" >>= parseExprLoc fuel
      pure (CallKwarg.mk key.nameId value)
    return .generalizedCall [] kwargsList
  | "ArgsKargs" => do
    -- ArgsKargs has positional args, optional *var_args, named kwargs, and
    -- optional **var_kwargs. We preserve named positional/keyword args
    -- whenever there are no unpacks; the codegen layer can then map them
    -- back to parameter positions by name. Unpacks (`*args`/`**kwargs`)
    -- still collapse to a single `PyVal.none` placeholder, since we have
    -- no way to statically expand them.
    let argsOpt ← fieldOpt val "args"
    let argsList ← match argsOpt with
      | some (.arr a) => parseList a (parseExprLoc fuel)
      | _ => pure []
    let hasVarArgs ← match ← fieldOpt val "var_args" with
      | some _ => pure true | none => pure false
    let kwargsOpt ← fieldOpt val "kwargs"
    let kwargsRawList ← match kwargsOpt with
      | some (.arr a) => pure a.toList
      | _ => pure []
    let hasVarKwargs ← match ← fieldOpt val "var_kwargs" with
      | some _ => pure true | none => pure false
    if hasVarArgs || hasVarKwargs then
      -- Fall back to legacy collapsing: 1 placeholder per affected group.
      let posGroup := if hasVarArgs then
        [ExprLoc.mk ⟨0, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩ (.literal .none)]
      else argsList
      let kwGroup := if hasVarKwargs || !kwargsRawList.isEmpty then
        [ExprLoc.mk ⟨0, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩ (.literal .none)]
      else []
      return .simple (posGroup ++ kwGroup)
    else
      -- No unpacks: parse named kwargs into CallKwarg so the codegen can
      -- bind them by parameter name at call sites.
      let posCallArgs := argsList.map CallArg.pos
      let kwargsList ← kwargsRawList.mapM fun kw => do
        let key ← field kw "key" >>= parseIdentifier
        let value ← field kw "value" >>= parseExprLoc fuel
        pure (CallKwarg.mk key.nameId value)
      return .generalizedCall posCallArgs kwargsList
  | "GeneralizedCall" => do
    let argsArr ← field val "args" >>= asArr
    let kwargsArr ← field val "kwargs" >>= asArr
    let args ← parseList argsArr (parseCallArg fuel)
    let kwargs ← parseList kwargsArr (parseCallKwarg fuel)
    return .generalizedCall args kwargs
  | "SingleKwarg" => do
    let arr ← asArr val
    match arr.toList with
    | [nameJ, exprJ] => return .singleKwarg (← asNat nameJ) (← parseExprLoc fuel exprJ)
    | _ => .error "ArgExprs::SingleKwarg must have exactly 2 elements"
  | _ => .error s!"unknown ArgExprs variant: {tag}"

private partial def parseCallArg (fuel : Nat) (j : Json) : ParseResult CallArg := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Value" => return .pos (← parseExprLoc fuel val)
  | "Unpack" => return .posUnpack (← parseExprLoc fuel val)
  | _ => .error s!"unknown CallArg variant: {tag}"

private partial def parseCallKwarg (fuel : Nat) (j : Json) : ParseResult CallKwarg := do
  let (tag, val) ← taggedVariant j
  match tag with
  | "Named" => do
    -- Named is a Kwarg struct: {key: Identifier, value: ExprLoc}
    let key ← field val "key" >>= parseIdentifier
    let value ← field val "value" >>= parseExprLoc fuel
    return .mk key.nameId value
  | "Unpack" => do
    -- **unpack: use placeholder name (0) since it's an unpack, not a named kwarg
    return .mk 0 (← parseExprLoc fuel val)
  | _ => .error s!"unknown CallKwarg variant: {tag}"

private partial def parseUnpackTarget (fuel : Nat) (j : Json) : ParseResult UnpackTarget :=
  match fuel with
  | 0 => .error "parse fuel exhausted"
  | fuel + 1 => do
    let (tag, val) ← taggedVariant j
    match tag with
    | "Name" => return .name (← parseIdentifier val)
    | "Tuple" => do
      let targets ← field val "targets" >>= asArr >>= fun a =>
        parseList a (parseUnpackTarget fuel)
      let pos ← field val "position" >>= parseCodeRange
      return .tuple targets pos
    | "Starred" => return .starred (← parseIdentifier val)
    | _ => .error s!"unknown UnpackTarget variant: {tag}"

private partial def parseExceptHandler (fuel : Nat) (j : Json) : ParseResult ExceptHandler := do
  let excType ← parseOptExprLoc fuel j "exc_type"
  let name ← match ← fieldOpt j "name" with
    | some v => pure (some (← parseIdentifier v))
    | none => pure none
  let body ← field j "body" >>= asArr >>= fun a => parseList a (parseNode fuel)
  return .mk excType name body

private partial def parseTryBlock (fuel : Nat) (j : Json) : ParseResult TryBlock := do
  let body ← field j "body" >>= asArr >>= fun a => parseList a (parseNode fuel)
  let handlers ← field j "handlers" >>= asArr >>= fun a =>
    parseList a (parseExceptHandler fuel)
  let orElse ← field j "or_else" >>= asArr >>= fun a => parseList a (parseNode fuel)
  let finallyBody ← field j "finally" >>= asArr >>= fun a => parseList a (parseNode fuel)
  return .mk body handlers orElse finallyBody

private partial def parseFunctionDef (fuel : Nat) (j : Json) : ParseResult FunctionDef := do
  let name ← field j "name" >>= parseIdentifier
  let sig ← field j "signature" >>= parseSignature
  let body ← field j "body" >>= asArr >>= fun a => parseList a (parseNode fuel)
  let nsSize ← field j "namespace_size" >>= asNat
  let freeVarSlots ← field j "free_var_enclosing_slots" >>= asArr >>= fun a =>
    parseList a asNat
  let cellVarCount ← field j "cell_var_count" >>= asNat
  let cellParamIndices ← field j "cell_param_indices" >>= asArr >>= fun a =>
    parseList a fun item =>
      match item with
      | .null => return none
      | _ => return some (← asNat item)
  let defaultExprs ← field j "default_exprs" >>= asArr >>= fun a =>
    parseList a (parseExprLoc fuel)
  let isAsync ← field j "is_async" >>= asBool
  let retAnn ← parseOptExprLoc fuel j "return_annotation"
  let paramAnns ← field j "param_annotations" >>= asArr >>= fun a =>
    parseList a fun item =>
      match item with
      | .null => return none
      | _ => return some (← parseExprLoc fuel item)
  let effectAnn ← field j "effect_annotation" >>= parseEffectAnnotation
  return .mk name sig body nsSize freeVarSlots cellVarCount cellParamIndices
    defaultExprs isAsync retAnn paramAnns effectAnn

private partial def parseNode (fuel : Nat) (j : Json) : ParseResult Node :=
  match fuel with
  | 0 => .error "parse fuel exhausted"
  | fuel + 1 => do
    let (tag, val) ← taggedVariant j
    match tag with
    | "Pass" => return .pass
    | "Expr" => return .expr (← parseExprLoc fuel val)
    | "Return" => return .ret (← parseExprLoc fuel val)
    | "ReturnNone" => return .retNone
    | "Raise" =>
      match val with
      | .null => return .raise none
      | _ => return .raise (some (← parseExprLoc fuel val))
    | "Assert" => do
      let test ← field val "test" >>= parseExprLoc fuel
      let msg ← parseOptExprLoc fuel val "msg"
      return .assert test msg
    | "Assign" => do
      let target ← field val "target" >>= parseIdentifier
      let obj ← field val "object" >>= parseExprLoc fuel
      return .assign target obj
    | "UnpackAssign" => do
      let targets ← field val "targets" >>= asArr >>= fun a =>
        parseList a (parseUnpackTarget fuel)
      let targetsPos ← field val "targets_position" >>= parseCodeRange
      let obj ← field val "object" >>= parseExprLoc fuel
      return .unpackAssign targets targetsPos obj
    | "OpAssign" => do
      let target ← field val "target" >>= parseIdentifier
      let op ← field val "op" >>= parseOperator
      let value ← field val "value" >>= parseExprLoc fuel
      return .opAssign target op value
    | "SubscriptOpAssign" => do
      let target ← field val "target" >>= parseExprLoc fuel
      let index ← field val "index" >>= parseExprLoc fuel
      let op ← field val "op" >>= parseOperator
      let value ← field val "value" >>= parseExprLoc fuel
      let targetPos ← field val "target_position" >>= parseCodeRange
      return .subscriptOpAssign target index op value targetPos
    | "SubscriptAssign" => do
      let target ← field val "target" >>= parseExprLoc fuel
      let index ← field val "index" >>= parseExprLoc fuel
      let value ← field val "value" >>= parseExprLoc fuel
      let targetPos ← field val "target_position" >>= parseCodeRange
      return .subscriptAssign target index value targetPos
    | "AttrOpAssign" => do
      let obj ← field val "object" >>= parseExprLoc fuel
      let attr ← field val "attr" >>= parseEitherStr
      let op ← field val "op" >>= parseOperator
      let value ← field val "value" >>= parseExprLoc fuel
      let targetPos ← field val "target_position" >>= parseCodeRange
      return .attrOpAssign obj attr op value targetPos
    | "AttrAssign" => do
      let obj ← field val "object" >>= parseExprLoc fuel
      let attr ← field val "attr" >>= parseEitherStr
      let targetPos ← field val "target_position" >>= parseCodeRange
      let value ← field val "value" >>= parseExprLoc fuel
      return .attrAssign obj attr targetPos value
    | "For" => do
      let target ← field val "target" >>= parseUnpackTarget fuel
      let iter ← field val "iter" >>= parseExprLoc fuel
      let body ← field val "body" >>= asArr >>= fun a => parseList a (parseNode fuel)
      let orElse ← field val "or_else" >>= asArr >>= fun a => parseList a (parseNode fuel)
      return .for target iter body orElse
    | "While" => do
      let test ← field val "test" >>= parseExprLoc fuel
      let body ← field val "body" >>= asArr >>= fun a => parseList a (parseNode fuel)
      let orElse ← field val "or_else" >>= asArr >>= fun a => parseList a (parseNode fuel)
      return .while test body orElse
    | "Break" => do
      let pos ← field val "position" >>= parseCodeRange
      return .break pos
    | "Continue" => do
      let pos ← field val "position" >>= parseCodeRange
      return .continue pos
    | "If" => do
      let test ← field val "test" >>= parseExprLoc fuel
      let body ← field val "body" >>= asArr >>= fun a => parseList a (parseNode fuel)
      let orElse ← field val "or_else" >>= asArr >>= fun a => parseList a (parseNode fuel)
      return .if test body orElse
    | "FunctionDef" => do
      let fd ← parseFunctionDef fuel val
      return .funcDef fd
    | "Global" => do
      let pos ← field val "position" >>= parseCodeRange
      let names ← field val "names" >>= asArr >>= fun a => parseList a asNat
      return .global pos names
    | "Nonlocal" => do
      let pos ← field val "position" >>= parseCodeRange
      let names ← field val "names" >>= asArr >>= fun a => parseList a asNat
      return .nonlocal pos names
    | "Try" => do
      let tb ← parseTryBlock fuel val
      return .try tb
    | "Import" => do
      let modName ← field val "module_name" >>= asNat
      let binding ← field val "binding" >>= parseIdentifier
      return .import modName binding
    | "ImportFrom" => do
      let modName ← field val "module_name" >>= asNat
      let namesArr ← field val "names" >>= asArr
      let names ← parseList namesArr fun item => do
        let arr ← asArr item
        match arr.toList with
        | [nameJ, bindJ] => return (← asNat nameJ, ← parseIdentifier bindJ)
        | _ => .error "ImportFrom name pair must have 2 elements"
      let pos ← field val "position" >>= parseCodeRange
      return .importFrom modName names pos
    | _ => .error s!"unknown Node variant: {tag}"

end -- mutual

-- ============================================================================
-- Top-level parse
-- ============================================================================

/-- Parse the JSON output of `monty::emit_ir_json` into an `IrExport`. -/
def parseIrExport (j : Json) : ParseResult IrExport := do
  let strTableArr ← field j "string_table" >>= asArr
  let strTable ← parseList strTableArr asStr
  let nodesArr ← field j "nodes" >>= asArr
  let nodes ← parseList nodesArr (parseNode defaultFuel)
  return ⟨strTable.toArray, nodes⟩

/-- Parse a JSON string into an `IrExport`. -/
def parseIrExportFromString (s : String) : ParseResult IrExport := do
  let json ← match Json.parse s with
    | .ok j => .ok j
    | .error e => .error s!"JSON parse error: {e}"
  parseIrExport json

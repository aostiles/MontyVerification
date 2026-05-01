/-!
# Monty IR Core Types

This module defines the Lean4 inductive types that mirror Monty's prepared IR
(`PreparedNode`, `Expr`, `Identifier`, etc.). These types are the foundation
for all verification: effect checking, protocol verification, and termination
analysis operate over these structures.

The types are designed to match the JSON output of `monty::emit_ir_json`,
which serializes the IR after the prepare phase (name resolution, scope
analysis) but before bytecode compilation.

## Design Principles

- **Structural fidelity**: Every Rust enum variant maps to a Lean constructor.
  The JSON serialization uses serde's default externally-tagged format, so
  variant names in Lean match the JSON keys exactly.

- **Omit runtime-only fields**: Source positions (`CodeRange`), namespace
  indices, and bind modes are captured as opaque types. They're needed for
  JSON parsing but irrelevant to verification.

- **Decidable equality**: All types derive `DecidableEq` where possible,
  enabling computational verification (the checker returns `Bool`, not `Prop`).
-/

-- ============================================================================
-- Base Types
-- ============================================================================

/-- Interned string identifier. In Monty's IR, all names (variables, functions,
    attributes, string literals) are represented as indices into a string table.
    The JSON export includes the string table so these can be resolved. -/
abbrev StringId := Nat

/-- Source position in the original Python code. Opaque in Lean — carried
    through for JSON round-tripping but not used in any verification proofs. -/
structure Position where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Source range with filename reference and preview line number. -/
structure CodeRange where
  filename : Nat
  previewLine : Nat
  start : Position
  «end» : Position
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Operators
-- ============================================================================

/-- Binary arithmetic and logical operators.
    Maps to `Operator` in `crates/monty/src/expressions.rs`. -/
inductive Operator where
  | add | sub | mult | matMult | div | «mod» | pow
  | lShift | rShift | bitOr | bitXor | bitAnd | floorDiv
  | «and» | «or»
  deriving Repr, DecidableEq, Inhabited

/-- Comparison operators. These always produce a `Bool` value.
    Maps to `CmpOperator` in `crates/monty/src/expressions.rs`. -/
inductive CmpOperator where
  | eq | notEq | lt | ltE | gt | gtE
  | «is» | isNot | «in» | notIn
  /-- Optimized modular equality: `x % n == 0`. The `Int` is the modulus. -/
  | modEq : Int → CmpOperator
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Name Resolution
-- ============================================================================

/-- Which namespace a variable reference was resolved to during the prepare phase. -/
inductive NameScope where
  | local
  | localUnassigned
  | global
  | cell
  deriving Repr, DecidableEq, Inhabited

/-- A resolved variable reference. -/
structure Identifier where
  position : CodeRange
  nameId : StringId
  optNamespaceId : Option Nat
  scope : NameScope
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Literals
-- ============================================================================

/-- Literal values known at parse time. -/
inductive Literal where
  | none | ellipsis
  | bool : Bool → Literal
  | int : Int → Literal
  | float : Float → Literal
  | str : StringId → Literal
  | bytes : Nat → Literal
  | longInt : Nat → Literal
  | marker : Nat → Literal
  deriving Repr, Inhabited

-- ============================================================================
-- Effects
-- ============================================================================

/-- A capability that a function may exercise during execution.
    Maps to `Effect` in `crates/monty/src/effects.rs`. -/
inductive Effect where
  | fs | net | env | time
  | custom : StringId → Effect
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

instance : ToString Effect where
  toString
    | .fs => "FS"
    | .net => "Net"
    | .env => "Env"
    | .time => "Time"
    | .custom id => s!"Custom({id})"

/-- Resolved effect annotation on a function's return type. -/
inductive EffectAnnotation where
  | pure
  | effectful : List Effect → EffectAnnotation
  | unannotated
  deriving Repr, DecidableEq, Inhabited, BEq

-- ============================================================================
-- Non-recursive helper types
-- ============================================================================

/-- Built-in function identifier. The string carries the Monty IR's
    builtin name (e.g. `"Len"`, `"Str"`, `"Abs"`, `"Min"`); the empty
    string is the legacy "opaque" placeholder used when the JSON parser
    can't extract a name. Codegen dispatches on this string to wire
    builtin calls to real semantics in `EffectMonad.lean` (`pyLen`,
    `pyAbs`, etc.) instead of the historical `pyLen`-for-everything
    fallback. -/
abbrev BuiltinId := String

/-- Target of a direct function call. -/
inductive Callable where
  | builtin : BuiltinId → Callable
  | name : Identifier → Callable
  deriving Repr, DecidableEq, Inhabited

/-- Bind mode for function signatures. -/
inductive BindMode where
  | simple | complexArgs
  deriving Repr, DecidableEq, Inhabited

/-- Function signature (parameter structure, no types). -/
structure Signature where
  posArgs : Option (List StringId)
  posDefaultsCount : Nat
  args : Option (List StringId)
  argDefaultsCount : Nat
  varArgs : Option StringId
  kwargs : Option (List StringId)
  kwargDefaultMap : Option (List (Option Nat))
  varKwargs : Option StringId
  bindMode : BindMode
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Mutually recursive AST types
-- ============================================================================

-- All types that reference each other (ExprLoc ↔ Expr ↔ Node ↔ FunctionDef)
-- must be in a single `mutual` block.
mutual

/-- An expression with source location. -/
inductive ExprLoc where
  | mk : CodeRange → Expr → ExprLoc

/-- An expression in the prepared IR. -/
inductive Expr where
  | literal : Literal → Expr
  | builtin : BuiltinId → Expr
  | name : Identifier → Expr
  | call : Callable → ArgExprs → Expr
  | attrCall : ExprLoc → StringId → ArgExprs → Expr
  | indirectCall : ExprLoc → ArgExprs → Expr
  | attrGet : ExprLoc → StringId → Expr
  | op : ExprLoc → Operator → ExprLoc → Expr
  | cmpOp : ExprLoc → CmpOperator → ExprLoc → Expr
  | chainCmp : ExprLoc → List (CmpOperator × ExprLoc) → Expr
  | list : List SequenceItem → Expr
  | tuple : List SequenceItem → Expr
  | dict : List DictItem → Expr
  | set : List SequenceItem → Expr
  | subscript : ExprLoc → ExprLoc → Expr
  | slice : Option ExprLoc → Option ExprLoc → Option ExprLoc → Expr
  | not : ExprLoc → Expr
  | unaryMinus : ExprLoc → Expr
  | unaryPlus : ExprLoc → Expr
  | unaryInvert : ExprLoc → Expr
  | «await» : ExprLoc → Expr
  | fstring : List FStringPart → Expr
  | ifElse : ExprLoc → ExprLoc → ExprLoc → Expr
  | listComp : ExprLoc → List Comprehension → Expr
  | setComp : ExprLoc → List Comprehension → Expr
  | dictComp : ExprLoc → ExprLoc → List Comprehension → Expr
  | lambda : FunctionDef → Expr
  | named : Identifier → ExprLoc → Expr

/-- An item in a list, tuple, or set literal. -/
inductive SequenceItem where
  | value : ExprLoc → SequenceItem
  | unpack : ExprLoc → SequenceItem

/-- An item in a dict literal. -/
inductive DictItem where
  | pair : ExprLoc → ExprLoc → DictItem
  | unpack : ExprLoc → DictItem

/-- Generator clause in a comprehension. -/
inductive Comprehension where
  | mk : UnpackTarget → ExprLoc → List ExprLoc → Comprehension

/-- F-string format specification. -/
inductive FStringFormatSpec where
  | literal : StringId → FStringFormatSpec
  | dynamic : ExprLoc → FStringFormatSpec

/-- F-string part: literal string or formatted value. -/
inductive FStringPart where
  | literal : StringId → FStringPart
  | value : ExprLoc → Option Nat → Option FStringFormatSpec → FStringPart

/-- Call argument (positional, keyword, or unpack). -/
inductive CallArg where
  | pos : ExprLoc → CallArg
  | posUnpack : ExprLoc → CallArg
  | kw : StringId → ExprLoc → CallArg
  | kwUnpack : ExprLoc → CallArg

/-- Keyword-only call argument. -/
inductive CallKwarg where
  | mk : StringId → ExprLoc → CallKwarg

/-- Call argument bundle. -/
inductive ArgExprs where
  | simple : List ExprLoc → ArgExprs
  | singleKwarg : StringId → ExprLoc → ArgExprs
  | generalizedCall : List CallArg → List CallKwarg → ArgExprs

/-- Unpack target in assignments and for loops. -/
inductive UnpackTarget where
  | name : Identifier → UnpackTarget
  | tuple : List UnpackTarget → CodeRange → UnpackTarget
  | starred : Identifier → UnpackTarget

/-- Exception handler clause in a try statement. -/
inductive ExceptHandler where
  | mk : Option ExprLoc → Option Identifier → List Node → ExceptHandler

/-- Try statement components. -/
inductive TryBlock where
  | mk : List Node → List ExceptHandler → List Node → List Node → TryBlock

/-- A prepared function definition with resolved names and effect annotations.
    Maps to `PreparedFunctionDef` in `crates/monty/src/expressions.rs`. -/
inductive FunctionDef where
  | mk :
    (name : Identifier) →
    (signature : Signature) →
    (body : List Node) →
    (namespaceSize : Nat) →
    (freeVarEnclosingSlots : List Nat) →
    (cellVarCount : Nat) →
    (cellParamIndices : List (Option Nat)) →
    (defaultExprs : List ExprLoc) →
    (isAsync : Bool) →
    (returnAnnotation : Option ExprLoc) →
    (paramAnnotations : List (Option ExprLoc)) →
    (effectAnnotation : EffectAnnotation) →
    FunctionDef

/-- A statement node in the prepared IR.
    Maps to `Node<PreparedFunctionDef>` in `crates/monty/src/expressions.rs`. -/
inductive Node where
  | pass
  | expr : ExprLoc → Node
  | ret : ExprLoc → Node
  | retNone
  | raise : Option ExprLoc → Node
  | assert : ExprLoc → Option ExprLoc → Node
  | assign : Identifier → ExprLoc → Node
  | unpackAssign : List UnpackTarget → CodeRange → ExprLoc → Node
  | opAssign : Identifier → Operator → ExprLoc → Node
  | subscriptOpAssign : ExprLoc → ExprLoc → Operator → ExprLoc → CodeRange → Node
  | subscriptAssign : ExprLoc → ExprLoc → ExprLoc → CodeRange → Node
  | attrOpAssign : ExprLoc → StringId → Operator → ExprLoc → CodeRange → Node
  | attrAssign : ExprLoc → StringId → CodeRange → ExprLoc → Node
  | «for» : UnpackTarget → ExprLoc → List Node → List Node → Node
  | «while» : ExprLoc → List Node → List Node → Node
  | «break» : CodeRange → Node
  | «continue» : CodeRange → Node
  | «if» : ExprLoc → List Node → List Node → Node
  | funcDef : FunctionDef → Node
  | global : CodeRange → List StringId → Node
  | nonlocal : CodeRange → List StringId → Node
  | «try» : TryBlock → Node
  | import : StringId → Identifier → Node
  | importFrom : StringId → List (StringId × Identifier) → CodeRange → Node

end -- mutual

-- ============================================================================
-- Accessors for mutual inductive types
-- ============================================================================

namespace ExprLoc
  def position : ExprLoc → CodeRange
    | .mk pos _ => pos
  def expr : ExprLoc → Expr
    | .mk _ e => e
end ExprLoc

namespace FunctionDef
  def name : FunctionDef → Identifier
    | .mk n .. => n
  def signature : FunctionDef → Signature
    | .mk _ s .. => s
  def body : FunctionDef → List Node
    | .mk _ _ b .. => b
  def defaultExprs : FunctionDef → List ExprLoc
    | .mk _ _ _ _ _ _ _ d .. => d
  def isAsync : FunctionDef → Bool
    | .mk _ _ _ _ _ _ _ _ a .. => a
  def returnAnnotation : FunctionDef → Option ExprLoc
    | .mk _ _ _ _ _ _ _ _ _ r .. => r
  def paramAnnotations : FunctionDef → List (Option ExprLoc)
    | .mk _ _ _ _ _ _ _ _ _ _ p _ => p
  def effectAnnotation : FunctionDef → EffectAnnotation
    | .mk _ _ _ _ _ _ _ _ _ _ _ e => e
end FunctionDef

namespace Comprehension
  def target : Comprehension → UnpackTarget
    | .mk t _ _ => t
  def iter : Comprehension → ExprLoc
    | .mk _ i _ => i
  def ifs : Comprehension → List ExprLoc
    | .mk _ _ is_ => is_
end Comprehension

namespace ExceptHandler
  def excType : ExceptHandler → Option ExprLoc
    | .mk t _ _ => t
  def name : ExceptHandler → Option Identifier
    | .mk _ n _ => n
  def body : ExceptHandler → List Node
    | .mk _ _ b => b
end ExceptHandler

namespace TryBlock
  def body : TryBlock → List Node
    | .mk b _ _ _ => b
  def handlers : TryBlock → List ExceptHandler
    | .mk _ h _ _ => h
  def orElse : TryBlock → List Node
    | .mk _ _ o _ => o
  def finallyBody : TryBlock → List Node
    | .mk _ _ _ f => f
end TryBlock

-- ============================================================================
-- Top-Level IR Export Structure
-- ============================================================================

/-- Self-contained IR export matching the JSON output of `monty::emit_ir_json`. -/
structure IrExport where
  stringTable : Array String
  nodes : List Node

/-- Look up a string by its `StringId`. Returns `"<unknown>"` if out of bounds. -/
def IrExport.resolveString (ir : IrExport) (id : StringId) : String :=
  if h : id < ir.stringTable.size then
    ir.stringTable[id]
  else
    "<unknown>"

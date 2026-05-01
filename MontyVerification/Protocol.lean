import MontyVerification.Basic
import MontyVerification.EffectInference

/-!
# Protocol Verification (Layer 2)

Verifies per-program properties about the *sequence* and *frequency* of
external function calls. Operates on traces extracted from the IR.

Uses call graph resolution (via `FuncTable`) to inline callee traces
when an internal function is called, ensuring protocol checks see the
*transitive* external calls through helper functions.
-/

-- ============================================================================
-- Trace Extraction
-- ============================================================================

/-- An external call event in a trace. -/
structure TraceEvent where
  functionName : StringId
  deriving Repr, BEq

/-- Extract the ordered sequence of external calls from a node list,
    resolving internal calls via the function table. -/
partial def extractNodeListCalls
    (env : TrustEnv) (funcTable : FuncTable) (visited : List StringId)
    (nodes : List Node) : List TraceEvent :=
  nodes.flatMap (extractNodeCalls env funcTable visited)
where
  extractNodeCalls (env : TrustEnv) (ft : FuncTable) (vis : List StringId) : Node → List TraceEvent
    | .expr e | .ret e | .assign _ e | .opAssign _ _ e | .unpackAssign _ _ e =>
      extractEL env ft vis e
    | .raise (some e) | .assert e none => extractEL env ft vis e
    | .assert t (some m) => extractEL env ft vis t ++ extractEL env ft vis m
    | .subscriptAssign t i v _ | .subscriptOpAssign t i _ v _ =>
      extractEL env ft vis t ++ extractEL env ft vis i ++ extractEL env ft vis v
    | .attrAssign o _ _ v | .attrOpAssign o _ _ v _ =>
      extractEL env ft vis o ++ extractEL env ft vis v
    | .«for» _ iter body orElse =>
      extractEL env ft vis iter ++ extractNL env ft vis body ++ extractNL env ft vis orElse
    | .«while» test body orElse =>
      extractEL env ft vis test ++ extractNL env ft vis body ++ extractNL env ft vis orElse
    | .«if» test body orElse =>
      extractEL env ft vis test ++ extractNL env ft vis body ++ extractNL env ft vis orElse
    | .«try» tb =>
      extractNL env ft vis tb.body ++ extractNL env ft vis tb.orElse ++ extractNL env ft vis tb.finallyBody ++
      tb.handlers.flatMap fun h => extractNL env ft vis h.body
    | _ => []

  extractNL (env : TrustEnv) (ft : FuncTable) (vis : List StringId) (nodes : List Node) : List TraceEvent :=
    nodes.flatMap (extractNodeCalls env ft vis)

  extractEL (env : TrustEnv) (ft : FuncTable) (vis : List StringId) (el : ExprLoc) : List TraceEvent :=
    extractE env ft vis el.expr

  extractE (env : TrustEnv) (ft : FuncTable) (vis : List StringId) : Expr → List TraceEvent
    | .call (.name id) args =>
      let argCalls := extractArgs env ft vis args
      match env.lookup id.nameId with
      | some _ =>
        -- External function: emit trace event
        argCalls ++ [{ functionName := id.nameId }]
      | none =>
        -- Internal call: inline callee's trace
        if vis.contains id.nameId then argCalls  -- cycle
        else match ft.find? (·.1 == id.nameId) with
          | some (_, fd) =>
            let calleeTable := ft ++ buildFuncTable fd.body
            argCalls ++ extractNL env calleeTable (id.nameId :: vis) fd.body
          | none => argCalls
    | .call (.builtin _) args => extractArgs env ft vis args
    | .attrCall obj _ args => extractEL env ft vis obj ++ extractArgs env ft vis args
    | .indirectCall callee args => extractEL env ft vis callee ++ extractArgs env ft vis args
    | .op l _ r => extractEL env ft vis l ++ extractEL env ft vis r
    | .cmpOp l _ r => extractEL env ft vis l ++ extractEL env ft vis r
    | .ifElse t b o => extractEL env ft vis t ++ extractEL env ft vis b ++ extractEL env ft vis o
    | .not e | .unaryMinus e | .unaryPlus e | .unaryInvert e | .await e => extractEL env ft vis e
    | .subscript o i => extractEL env ft vis o ++ extractEL env ft vis i
    | .named _ v => extractEL env ft vis v
    | .lambda fd =>
      let calleeTable := ft ++ buildFuncTable fd.body
      extractNL env calleeTable vis fd.body
    | .chainCmp l cs => extractEL env ft vis l ++ cs.flatMap fun (_, e) => extractEL env ft vis e
    | .list items | .tuple items | .set items =>
      items.flatMap fun | .value e | .unpack e => extractEL env ft vis e
    | .dict items =>
      items.flatMap fun
        | .pair k v => extractEL env ft vis k ++ extractEL env ft vis v
        | .unpack e => extractEL env ft vis e
    | .fstring parts =>
      parts.flatMap fun | .literal _ => [] | .value e _ _ => extractEL env ft vis e
    | .attrGet o _ => extractEL env ft vis o
    | .slice l u s =>
      (l.map (extractEL env ft vis) |>.getD []) ++
      (u.map (extractEL env ft vis) |>.getD []) ++
      (s.map (extractEL env ft vis) |>.getD [])
    | .listComp elt gens | .setComp elt gens =>
      extractEL env ft vis elt ++ gens.flatMap fun c =>
        extractEL env ft vis c.iter ++ c.ifs.flatMap (extractEL env ft vis)
    | .dictComp k v gens =>
      extractEL env ft vis k ++ extractEL env ft vis v ++ gens.flatMap fun c =>
        extractEL env ft vis c.iter ++ c.ifs.flatMap (extractEL env ft vis)
    | _ => []

  extractArgs (env : TrustEnv) (ft : FuncTable) (vis : List StringId) : ArgExprs → List TraceEvent
    | .simple exprs => exprs.flatMap (extractEL env ft vis)
    | .singleKwarg _ v => extractEL env ft vis v
    | .generalizedCall args kwargs =>
      args.flatMap (fun
        | .pos e | .posUnpack e | .kwUnpack e => extractEL env ft vis e
        | .kw _ e => extractEL env ft vis e) ++
      kwargs.flatMap (fun | .mk _ e => extractEL env ft vis e)

-- ============================================================================
-- Protocol Primitives
-- ============================================================================

/-- A protocol is a named predicate on call traces. -/
structure Protocol where
  name : String
  check : List TraceEvent → Bool

/-- Require that function `before` appears before function `after` in the trace. -/
def requiresBefore (before after : StringId) (ir : IrExport) : Protocol where
  name := s!"requires '{ir.resolveString before}' before '{ir.resolveString after}'"
  check := fun trace =>
    match trace.findIdx? (·.functionName == after) with
    | none => true
    | some afterIdx =>
      match trace.findIdx? (·.functionName == before) with
      | none => false
      | some beforeIdx => beforeIdx < afterIdx

/-- Require that function `f` is called at most `n` times. -/
def maxCalls (f : StringId) (n : Nat) (ir : IrExport) : Protocol where
  name := s!"'{ir.resolveString f}' called at most {n} times"
  check := fun trace =>
    (trace.filter (·.functionName == f)).length <= n

/-- Require that function `f` is called at least once. -/
def mustCall (f : StringId) (ir : IrExport) : Protocol where
  name := s!"must call '{ir.resolveString f}'"
  check := fun trace =>
    trace.any (·.functionName == f)

/-- Verify a protocol against a function's call trace.
    Builds a function table to resolve internal calls transitively. -/
def verifyProtocol (env : TrustEnv) (ir : IrExport) (fd : FunctionDef) (p : Protocol) : Bool :=
  let funcTable := buildFuncTable fd.body
  let trace := extractNodeListCalls env funcTable [] fd.body
  p.check trace

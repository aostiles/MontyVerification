import MontyVerification.Basic

/-!
# Effect Inference

Infers the effect set of a function body by walking the IR and collecting
all external call effects. This is the core of Layer 1 verification.

## Trust Model

Effect inference relies on a `TrustEnv` that maps external function names
to their declared effect sets. These declarations are **trusted** (the host
vouches for them). The inference then **verifies** that user code's declared
effects match what the body actually does.

## Call Graph Resolution

When a function calls another locally-defined function (not an external),
the inference recursively walks the callee's body to propagate its effects.
This prevents attackers from hiding external calls in helper functions.
A visited set prevents infinite recursion on self-recursive or mutually-recursive
functions.
-/

-- ============================================================================
-- Trust Environment
-- ============================================================================

/-- Maps external function names (StringIds) to their declared effect sets. -/
structure TrustEnv where
  lookup : StringId → Option (List Effect)

/-- Create a trust environment from a list of (name, effects) pairs. -/
def TrustEnv.fromList (entries : List (StringId × List Effect)) : TrustEnv :=
  { lookup := fun id => entries.find? (·.1 == id) |>.map (·.2) }

-- ============================================================================
-- Function Table
-- ============================================================================

/-- Maps function name StringIds to their definitions, for resolving internal calls. -/
abbrev FuncTable := List (StringId × FunctionDef)

/-- Build a function table by scanning a node list for all FunctionDef nodes,
    including those nested inside other function bodies, loops, conditionals, etc.
    The table is flat — all functions at all nesting levels are included. -/
partial def buildFuncTable : List Node → FuncTable
  | [] => []
  | .funcDef fd :: rest =>
    -- Register this function and also scan its body for nested functions
    (fd.name.nameId, fd) :: buildFuncTable fd.body ++ buildFuncTable rest
  | .«for» _ _ body orElse :: rest =>
    buildFuncTable body ++ buildFuncTable orElse ++ buildFuncTable rest
  | .«while» _ body orElse :: rest =>
    buildFuncTable body ++ buildFuncTable orElse ++ buildFuncTable rest
  | .«if» _ body orElse :: rest =>
    buildFuncTable body ++ buildFuncTable orElse ++ buildFuncTable rest
  | .«try» tb :: rest =>
    buildFuncTable tb.body ++ buildFuncTable tb.orElse ++ buildFuncTable tb.finallyBody ++
    tb.handlers.flatMap (fun h => buildFuncTable h.body) ++ buildFuncTable rest
  | _ :: rest => buildFuncTable rest

-- ============================================================================
-- Inferred Effects
-- ============================================================================

/-- The result of effect inference on a function body. -/
structure InferredEffects where
  effects : List Effect
  externalCalls : List StringId

instance : Append InferredEffects where
  append a b := { effects := a.effects ++ b.effects, externalCalls := a.externalCalls ++ b.externalCalls }

def InferredEffects.empty : InferredEffects := { effects := [], externalCalls := [] }

instance : Inhabited InferredEffects := ⟨.empty⟩

def InferredEffects.dedup (ie : InferredEffects) : InferredEffects :=
  { effects := ie.effects.eraseDups, externalCalls := ie.externalCalls.eraseDups }

def InferredEffects.isSubsetOf (inferred : InferredEffects) (declared : List Effect) : Bool :=
  inferred.effects.all fun e => declared.contains e

def InferredEffects.isPure (ie : InferredEffects) : Bool :=
  ie.effects.isEmpty

-- ============================================================================
-- Effect inference walkers with call graph resolution
-- ============================================================================

/-- Infer effects from a list of nodes, resolving internal function calls
    via the function table. The visited set prevents infinite recursion
    on recursive/mutually-recursive functions. -/
partial def inferNodeListEffects
    (env : TrustEnv) (funcTable : FuncTable) (visited : List StringId)
    (nodes : List Node) : InferredEffects :=
  nodes.foldl (fun acc n => acc ++ inferNodeEffects env funcTable visited n) .empty
where
  inferNodeEffects (env : TrustEnv) (ft : FuncTable) (vis : List StringId) : Node → InferredEffects
    | .expr e | .ret e => inferEL env ft vis e
    | .assign _ e | .opAssign _ _ e | .unpackAssign _ _ e => inferEL env ft vis e
    | .raise (some e) => inferEL env ft vis e
    | .assert test msg =>
      inferEL env ft vis test ++ (msg.map (inferEL env ft vis) |>.getD .empty)
    | .subscriptAssign t i v _ | .subscriptOpAssign t i _ v _ =>
      inferEL env ft vis t ++ inferEL env ft vis i ++ inferEL env ft vis v
    | .attrAssign o _ _ v | .attrOpAssign o _ _ v _ =>
      inferEL env ft vis o ++ inferEL env ft vis v
    | .«for» _ iter body orElse =>
      inferEL env ft vis iter ++ inferNL env ft vis body ++ inferNL env ft vis orElse
    | .«while» test body orElse =>
      inferEL env ft vis test ++ inferNL env ft vis body ++ inferNL env ft vis orElse
    | .«if» test body orElse =>
      inferEL env ft vis test ++ inferNL env ft vis body ++ inferNL env ft vis orElse
    | .«try» tb =>
      inferNL env ft vis tb.body ++ inferNL env ft vis tb.orElse ++ inferNL env ft vis tb.finallyBody ++
      tb.handlers.foldl (fun acc h => acc ++ inferNL env ft vis h.body) .empty
    | .funcDef _ => .empty  -- defining a function has no effects; body resolved on call
    | _ => .empty

  inferNL (env : TrustEnv) (ft : FuncTable) (vis : List StringId) (nodes : List Node) : InferredEffects :=
    nodes.foldl (fun acc n => acc ++ inferNodeEffects env ft vis n) .empty

  inferEL (env : TrustEnv) (ft : FuncTable) (vis : List StringId) (el : ExprLoc) : InferredEffects :=
    inferE env ft vis el.expr

  inferE (env : TrustEnv) (ft : FuncTable) (vis : List StringId) : Expr → InferredEffects
    | .call (.name id) args =>
      let argEff := inferArgs env ft vis args
      match env.lookup id.nameId with
      | some effs =>
        -- External function: use declared effects
        argEff ++ { effects := effs, externalCalls := [id.nameId] }
      | none =>
        -- Internal call: resolve via function table
        if vis.contains id.nameId then
          argEff  -- cycle detected: don't recurse further
        else match ft.find? (·.1 == id.nameId) with
          | some (_, fd) =>
            -- Recursively infer callee's effects, adding to visited set
            let calleeTable := ft ++ buildFuncTable fd.body
            argEff ++ inferNL env calleeTable (id.nameId :: vis) fd.body
          | none => argEff  -- unknown function (builtin, input, etc.)
    | .call (.builtin _) args => inferArgs env ft vis args
    | .attrCall obj _ args => inferEL env ft vis obj ++ inferArgs env ft vis args
    | .indirectCall callee args => inferEL env ft vis callee ++ inferArgs env ft vis args
    | .op l _ r => inferEL env ft vis l ++ inferEL env ft vis r
    | .cmpOp l _ r => inferEL env ft vis l ++ inferEL env ft vis r
    | .not e | .unaryMinus e | .unaryPlus e | .unaryInvert e | .await e => inferEL env ft vis e
    | .ifElse t b o => inferEL env ft vis t ++ inferEL env ft vis b ++ inferEL env ft vis o
    | .subscript o i => inferEL env ft vis o ++ inferEL env ft vis i
    | .named _ v => inferEL env ft vis v
    | .lambda fd =>
      let calleeTable := ft ++ buildFuncTable fd.body
      inferNL env calleeTable vis fd.body
    | .chainCmp l cs =>
      inferEL env ft vis l ++ cs.foldl (fun acc (_, e) => acc ++ inferEL env ft vis e) .empty
    | .list items | .tuple items | .set items =>
      items.foldl (fun acc i => acc ++ match i with
        | .value e | .unpack e => inferEL env ft vis e) .empty
    | .dict items =>
      items.foldl (fun acc i => acc ++ match i with
        | .pair k v => inferEL env ft vis k ++ inferEL env ft vis v
        | .unpack e => inferEL env ft vis e) .empty
    | .listComp elt gens | .setComp elt gens =>
      inferEL env ft vis elt ++ gens.foldl (fun acc c =>
        acc ++ inferEL env ft vis c.iter ++ c.ifs.foldl (fun a e => a ++ inferEL env ft vis e) .empty) .empty
    | .dictComp k v gens =>
      inferEL env ft vis k ++ inferEL env ft vis v ++ gens.foldl (fun acc c =>
        acc ++ inferEL env ft vis c.iter ++ c.ifs.foldl (fun a e => a ++ inferEL env ft vis e) .empty) .empty
    | .fstring parts =>
      parts.foldl (fun acc p => acc ++ match p with
        | .literal _ => .empty
        | .value e _ _ => inferEL env ft vis e) .empty
    | .attrGet o _ => inferEL env ft vis o
    | .slice l u s =>
      (l.map (inferEL env ft vis) |>.getD .empty) ++
      (u.map (inferEL env ft vis) |>.getD .empty) ++
      (s.map (inferEL env ft vis) |>.getD .empty)
    | _ => .empty

  inferArgs (env : TrustEnv) (ft : FuncTable) (vis : List StringId) : ArgExprs → InferredEffects
    | .simple exprs => exprs.foldl (fun acc e => acc ++ inferEL env ft vis e) .empty
    | .singleKwarg _ v => inferEL env ft vis v
    | .generalizedCall args kwargs =>
      args.foldl (fun acc a => acc ++ match a with
        | .pos e | .posUnpack e | .kwUnpack e => inferEL env ft vis e
        | .kw _ e => inferEL env ft vis e) .empty ++
      kwargs.foldl (fun acc k => acc ++ match k with
        | .mk _ e => inferEL env ft vis e) .empty

-- ============================================================================
-- Effect Checking
-- ============================================================================

/-- Result of checking a function's effect annotation against its body. -/
inductive EffectCheckResult where
  | ok : EffectCheckResult
  | error : String → EffectCheckResult
  deriving Repr

/-- Check that a function's declared effect annotation matches its inferred effects.
    Builds a function table from the function body to resolve internal calls. -/
def checkFunctionEffects (env : TrustEnv) (ir : IrExport) (fd : FunctionDef) : EffectCheckResult :=
  let funcTable := buildFuncTable fd.body
  let inferred := (inferNodeListEffects env funcTable [] fd.body).dedup
  let name := ir.resolveString fd.name.nameId
  match fd.effectAnnotation with
  | .unannotated => .ok
  | .pure =>
    if inferred.isPure then .ok
    else .error s!"function '{name}' declared Pure but has effects: {inferred.effects.map toString}"
  | .effectful declared =>
    if inferred.isSubsetOf declared then .ok
    else
      let extra := inferred.effects.filter fun e => !declared.contains e
      .error s!"function '{name}' has undeclared effects: {extra.map toString}"

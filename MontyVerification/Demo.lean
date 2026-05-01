import MontyVerification.Basic
import MontyVerification.JsonDeser
import MontyVerification.EffectInference
import MontyVerification.Protocol

/-!
# Demo: Verifying AI Agent Programs

Runs the full verification pipeline on a parsed IR:
- Layer 1: Effect annotation checking (declared vs inferred effects)
- Layer 2: Protocol verification (call ordering, frequency, required calls)

The trust environment and protocol checks are configured based on which
external functions are found in the string table.
-/

/-- Build a trust environment from the IR, looking up known external functions. -/
def buildTrustEnv (ir : IrExport) : TrustEnv × List (String × StringId) :=
  let knownExternals : List (String × List Effect) := [
    ("search_web", [Effect.net]),
    ("send_email", [Effect.net]),
    ("read_file",  [Effect.fs]),
    ("write_file", [Effect.fs]),
    ("get_env",    [Effect.env])
  ]
  let resolved := knownExternals.filterMap fun (name, effs) =>
    (ir.stringTable.toList.findIdx? (· == name)).map fun id => (name, id, effs)
  let entries := resolved.map fun (_, id, effs) => (id, effs)
  let found := resolved.map fun (name, id, _) => (name, id)
  (TrustEnv.fromList entries, found)

/-- Run the full verification demo on the parsed IR. -/
def runDemo (ir : IrExport) : IO Unit := do
  let (env, foundExternals) := buildTrustEnv ir

  IO.println "=== Trust Environment ==="
  for (name, id) in foundExternals do
    let effs := match env.lookup id with
      | some e => String.intercalate ", " (e.map toString)
      | none => "?"
    IO.println s!"  {name} (id={id}): [{effs}]"

  -- Extract function definitions
  let funcs := ir.nodes.filterMap fun
    | .funcDef fd => some fd
    | _ => none

  IO.println s!"\n=== Functions Found: {funcs.length} ==="

  -- Layer 1: Effect Checking
  IO.println "\n=== Layer 1: Effect Annotation Verification ==="
  let mut layer1Pass := 0
  let mut layer1Fail := 0
  for fd in funcs do
    let name := ir.resolveString fd.name.nameId
    let funcTable := buildFuncTable fd.body
    let inferred := (inferNodeListEffects env funcTable [] fd.body).dedup
    let effAnnStr := match fd.effectAnnotation with
      | .pure => "Pure"
      | .effectful effs => s!"Effect[{String.intercalate ", " (effs.map toString)}]"
      | .unannotated => "(none)"
    let inferredStr := if inferred.isPure then "Pure"
      else s!"[{String.intercalate ", " (inferred.effects.map toString)}]"
    let result := checkFunctionEffects env ir fd
    match result with
    | .ok =>
      layer1Pass := layer1Pass + 1
      IO.println s!"  ✓ {name}: declared={effAnnStr}, inferred={inferredStr}"
    | .error msg =>
      layer1Fail := layer1Fail + 1
      IO.println s!"  ✗ {name}: declared={effAnnStr}, inferred={inferredStr}"
      IO.println s!"    VIOLATION: {msg}"

  IO.println s!"\n  Layer 1 summary: {layer1Pass} passed, {layer1Fail} FAILED"

  -- Layer 2: Protocol Verification
  -- Check protocols on every function that has Net effects (calls externals)
  IO.println "\n=== Layer 2: Protocol Verification ==="

  -- Find StringIds for protocol targets
  let searchWebId := (foundExternals.find? fun (n, _) => n == "search_web").map (·.2)
  let sendEmailId := (foundExternals.find? fun (n, _) => n == "send_email").map (·.2)

  let mut layer2Pass := 0
  let mut layer2Fail := 0

  for fd in funcs do
    let name := ir.resolveString fd.name.nameId
    let ft := buildFuncTable fd.body
    let trace := extractNodeListCalls env ft [] fd.body
    if trace.isEmpty then continue  -- skip pure functions for protocol checks
    IO.println s!"\n  Function: {name}"
    IO.println s!"  Call trace: {trace.map fun t => ir.resolveString t.functionName}"

    -- Protocol checks (only when both externals exist)
    if let (some swId, some seId) := (searchWebId, sendEmailId) then
      -- P1: search_web before send_email
      let p1 := requiresBefore swId seId ir
      let r1 := verifyProtocol env ir fd p1
      if r1 then layer2Pass := layer2Pass + 1
      else layer2Fail := layer2Fail + 1
      IO.println s!"    {if r1 then "✓" else "✗"} {p1.name}"

      -- P2: send_email at most once
      let p2 := maxCalls seId 1 ir
      let r2 := verifyProtocol env ir fd p2
      if r2 then layer2Pass := layer2Pass + 1
      else layer2Fail := layer2Fail + 1
      IO.println s!"    {if r2 then "✓" else "✗"} {p2.name}"

      -- P3: must call search_web
      let p3 := mustCall swId ir
      let r3 := verifyProtocol env ir fd p3
      if r3 then layer2Pass := layer2Pass + 1
      else layer2Fail := layer2Fail + 1
      IO.println s!"    {if r3 then "✓" else "✗"} {p3.name}"

  IO.println s!"\n  Layer 2 summary: {layer2Pass} passed, {layer2Fail} FAILED"

  -- Final summary
  let totalFail := layer1Fail + layer2Fail
  IO.println s!"\n=== {if totalFail == 0 then "✓ All checks passed" else s!"✗ {totalFail} violations found"} ==="

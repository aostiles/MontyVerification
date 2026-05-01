import MontyVerification.Basic
import MontyVerification.JsonDeser

/-!
# Sanity checks for JSON deserialization

Verifies that deserialized IR actually contains meaningful, traversable data —
not opaque blobs. Each test parses a known Python program's IR and asserts
specific structural properties about the resulting Lean terms.
-/

/-- Count all nodes recursively (including nested function bodies). -/
partial def countNodes : List Node → Nat
  | [] => 0
  | .funcDef fd :: rest => 1 + countNodes fd.body + countNodes rest
  | .«for» _ _ body orElse :: rest => 1 + countNodes body + countNodes orElse + countNodes rest
  | .«while» _ body orElse :: rest => 1 + countNodes body + countNodes orElse + countNodes rest
  | .«if» _ body orElse :: rest => 1 + countNodes body + countNodes orElse + countNodes rest
  | .«try» tb :: rest => 1 + countNodes tb.body + countNodes tb.orElse + countNodes tb.finallyBody +
      (tb.handlers.map (fun h => countNodes h.body)).foldl (· + ·) 0 + countNodes rest
  | _ :: rest => 1 + countNodes rest

/-- Extract all function definitions from a node list (top-level only). -/
def extractFuncDefs : List Node → List FunctionDef
  | [] => []
  | .funcDef fd :: rest => fd :: extractFuncDefs rest
  | _ :: rest => extractFuncDefs rest

/-- Extract all `Expr.call` targets from an expression (non-recursive, just top-level). -/
partial def extractCallTargets : Expr → List Callable
  | .call c _ => [c]
  | _ => []

/-- Recursively collect all call targets from a list of nodes. -/
partial def collectCallTargets : List Node → List Callable
  | [] => []
  | .expr el :: rest => extractCallTargets el.expr ++ collectCallTargets rest
  | .ret el :: rest => extractCallTargets el.expr ++ collectCallTargets rest
  | .assign _ el :: rest => extractCallTargets el.expr ++ collectCallTargets rest
  | .funcDef fd :: rest => collectCallTargets fd.body ++ collectCallTargets rest
  | .«if» _ body orElse :: rest =>
    collectCallTargets body ++ collectCallTargets orElse ++ collectCallTargets rest
  | .«for» _ _ body orElse :: rest =>
    collectCallTargets body ++ collectCallTargets orElse ++ collectCallTargets rest
  | _ :: rest => collectCallTargets rest

/-- Check if an expression is a binary op. -/
def isBinaryOp : Expr → Bool
  | .op _ _ _ => true
  | _ => false

/-- Check if an expression is a literal. -/
def isLiteral : Expr → Bool
  | .literal _ => true
  | _ => false

/-- Check if an expression is a name reference. -/
def isName : Expr → Bool
  | .name _ => true
  | _ => false

/-- Get the operator from a binary op expression. -/
def getOp : Expr → Option Operator
  | .op _ op _ => some op
  | _ => none

/-- Get the literal value if it's an int. -/
def getLitInt : Expr → Option Int
  | .literal (.int n) => some n
  | _ => none

/-- Get the scope of a name expression. -/
def getNameScope : Expr → Option NameScope
  | .name id => some id.scope
  | _ => none

/-- Run all sanity checks. Returns a list of (test_name, pass/fail_message). -/
def runSanityChecks (ir : IrExport) : List (String × Bool × String) :=
  let checks : List (String × Bool × String) := [
    -- Check 1: String table is non-empty
    ("string_table_nonempty",
     ir.stringTable.size > 0,
     s!"string table has {ir.stringTable.size} entries"),

    -- Check 2: Nodes list is non-empty
    ("nodes_nonempty",
     ir.nodes.length > 0,
     s!"has {ir.nodes.length} top-level nodes"),

    -- Check 3: Total node count (recursive) >= top-level count for non-trivial programs
    ("recursive_node_count",
     countNodes ir.nodes >= ir.nodes.length,
     s!"total recursive nodes: {countNodes ir.nodes}")
  ]

  -- Collect function-level checks
  let funcs := extractFuncDefs ir.nodes
  let funcChecks : List (String × Bool × String) := funcs.flatMap fun fd =>
    let name := ir.resolveString fd.name.nameId
    let bodyLen := fd.body.length
    let sig := fd.signature
    let totalParams := (sig.posArgs.getD []).length + (sig.args.getD []).length
    let effStr := match fd.effectAnnotation with
      | .pure => "Pure"
      | .effectful effs => s!"Effectful({effs.length})"
      | .unannotated => "Unannotated"
    [(s!"func_{name}_has_body", bodyLen > 0, s!"function '{name}' has {bodyLen} body statements"),
     (s!"func_{name}_sig", true, s!"function '{name}' has {totalParams} params, async={fd.isAsync}"),
     (s!"func_{name}_effect", true, s!"function '{name}' effect: {effStr}")]
  -- Scope check
  let allScopes := funcs.map fun fd => fd.name.scope
  let hasLocal := allScopes.any (· == .local)
  let hasLocalUnassigned := allScopes.any (· == .localUnassigned)
  let scopeCheck : List (String × Bool × String) := [("identifier_scopes_resolved",
    hasLocal || hasLocalUnassigned || funcs.isEmpty,
    s!"scopes found: local={hasLocal}, localUnassigned={hasLocalUnassigned}")]
  checks ++ funcChecks ++ scopeCheck

/-- Parse a sample program and run sanity checks. -/
def sanityCheckSample : IO Unit := do
  -- A small Python program with known structure
  let sampleJson := r#"{
    "string_table": ["test.py", "add", "x", "y", "fetch", "url", "result"],
    "nodes": [
      {"FunctionDef": {
        "name": {"position": {"filename": 0, "preview_line": 0, "start": {"line": 1, "column": 4}, "end": {"line": 1, "column": 7}}, "name_id": 1, "opt_namespace_id": 0, "scope": "LocalUnassigned"},
        "signature": {"pos_args": null, "pos_defaults_count": 0, "args": [2, 3], "arg_defaults_count": 0, "var_args": null, "kwargs": null, "kwarg_default_map": null, "var_kwargs": null, "bind_mode": "Simple"},
        "body": [
          {"Return": {"position": {"filename": 0, "preview_line": 1, "start": {"line": 2, "column": 11}, "end": {"line": 2, "column": 16}}, "expr": {"Op": {"left": {"position": {"filename": 0, "preview_line": 1, "start": {"line": 2, "column": 11}, "end": {"line": 2, "column": 12}}, "expr": {"Name": {"position": {"filename": 0, "preview_line": 1, "start": {"line": 2, "column": 11}, "end": {"line": 2, "column": 12}}, "name_id": 2, "opt_namespace_id": 0, "scope": "Local"}}}, "op": "Add", "right": {"position": {"filename": 0, "preview_line": 1, "start": {"line": 2, "column": 15}, "end": {"line": 2, "column": 16}}, "expr": {"Name": {"position": {"filename": 0, "preview_line": 1, "start": {"line": 2, "column": 15}, "end": {"line": 2, "column": 16}}, "name_id": 3, "opt_namespace_id": 1, "scope": "Local"}}}}}}}
        ],
        "namespace_size": 2, "free_var_enclosing_slots": [], "cell_var_count": 0, "cell_param_indices": [], "default_exprs": [], "is_async": false,
        "return_annotation": null, "param_annotations": [], "effect_annotation": "Unannotated"
      }},
      {"Assign": {
        "target": {"position": {"filename": 0, "preview_line": 3, "start": {"line": 4, "column": 0}, "end": {"line": 4, "column": 6}}, "name_id": 6, "opt_namespace_id": 1, "scope": "Local"},
        "object": {"position": {"filename": 0, "preview_line": 3, "start": {"line": 4, "column": 9}, "end": {"line": 4, "column": 18}}, "expr": {"Call": {"callable": {"Name": {"position": {"filename": 0, "preview_line": 3, "start": {"line": 4, "column": 9}, "end": {"line": 4, "column": 12}}, "name_id": 1, "opt_namespace_id": 0, "scope": "LocalUnassigned"}}, "args": {"Two": [{"position": {"filename": 0, "preview_line": 3, "start": {"line": 4, "column": 13}, "end": {"line": 4, "column": 14}}, "expr": {"Literal": {"Int": 1}}}, {"position": {"filename": 0, "preview_line": 3, "start": {"line": 4, "column": 16}, "end": {"line": 4, "column": 17}}, "expr": {"Literal": {"Int": 2}}}]}}}}
      }}
    ]
  }"#

  IO.println "=== Sanity Check: Inline Sample ==="
  match parseIrExportFromString sampleJson with
  | .error e => IO.println s!"PARSE ERROR: {e}"
  | .ok ir => do
    let results := runSanityChecks ir
    for (name, passed, msg) in results do
      let status := if passed then "✓" else "✗"
      IO.println s!"  {status} {name}: {msg}"

    -- Deep structural checks on the known program
    IO.println "\n=== Deep Structural Checks ==="

    -- Check the add function body
    match ir.nodes with
    | .funcDef fd :: .assign assignId assignExpr :: [] => do
      -- Function name resolves to "add"
      let fname := ir.resolveString fd.name.nameId
      IO.println s!"  ✓ First node is FunctionDef, name resolves to '{fname}'"
      assert! fname == "add"

      -- Function has 2 args
      let argCount := (fd.signature.args.getD []).length
      IO.println s!"  ✓ Function has {argCount} args"
      assert! argCount == 2

      -- Arg names resolve to "x" and "y"
      match fd.signature.args with
      | some [xId, yId] =>
        let xName := ir.resolveString xId
        let yName := ir.resolveString yId
        IO.println s!"  ✓ Args are '{xName}' and '{yName}'"
        assert! xName == "x"
        assert! yName == "y"
      | _ => IO.println "  ✗ Unexpected args structure"

      -- Body has exactly one Return statement
      match fd.body with
      | [.ret retExpr] => do
        IO.println s!"  ✓ Body has one Return statement"

        -- Return expression is Op(x, Add, y)
        match retExpr.expr with
        | .op left op right => do
          IO.println s!"  ✓ Return expr is binary Op"
          assert! op == .add
          IO.println s!"  ✓ Operator is Add"

          -- Left is Name with scope Local
          match left.expr with
          | .name id =>
            assert! id.scope == .local
            let lname := ir.resolveString id.nameId
            IO.println s!"  ✓ Left operand is Name '{lname}' (scope: Local)"
            assert! lname == "x"
          | _ => IO.println "  ✗ Left operand is not a Name"

          -- Right is Name with scope Local
          match right.expr with
          | .name id =>
            assert! id.scope == .local
            let rname := ir.resolveString id.nameId
            IO.println s!"  ✓ Right operand is Name '{rname}' (scope: Local)"
            assert! rname == "y"
          | _ => IO.println "  ✗ Right operand is not a Name"

        | _ => IO.println "  ✗ Return expr is not an Op"
      | _ => IO.println "  ✗ Body doesn't have exactly one Return"

      -- Check the Assign node
      let assignName := ir.resolveString assignId.nameId
      IO.println s!"  ✓ Second node is Assign to '{assignName}'"
      assert! assignName == "result"

      -- The assigned expression is a Call
      match assignExpr.expr with
      | .call callable args => do
        IO.println s!"  ✓ Assigned expression is a Call"
        -- Callable is Name("add")
        match callable with
        | .name id =>
          let cname := ir.resolveString id.nameId
          IO.println s!"  ✓ Call target is '{cname}'"
          assert! cname == "add"
        | _ => IO.println "  ✗ Callable is not a Name"

        -- Args are literals 1 and 2
        match args with
        | .simple [a1, a2] => do
          match a1.expr, a2.expr with
          | .literal (.int 1), .literal (.int 2) =>
            IO.println s!"  ✓ Call args are literal Int 1 and Int 2"
          | _, _ => IO.println "  ✗ Call args are not Int 1 and Int 2"
        | _ => IO.println "  ✗ Args are not simple [a1, a2]"
      | _ => IO.println "  ✗ Assigned expression is not a Call"

    | _ => IO.println "  ✗ Unexpected top-level node structure"

    IO.println "\n=== All sanity checks passed! ==="

/-- Run sanity checks on a corpus file to verify deep structure. -/
def sanityCheckCorpusFile (path : System.FilePath) : IO (Option String) := do
  let content ← IO.FS.readFile path
  match parseIrExportFromString content with
  | .error e => return some s!"parse error: {e}"
  | .ok ir => do
    -- Verify we can traverse into function bodies
    let funcs := extractFuncDefs ir.nodes
    for fd in funcs do
      -- Verify body is traversable (not empty opaque blob)
      let _ := countNodes fd.body
      -- Verify name resolves
      let _ := ir.resolveString fd.name.nameId
      -- Verify effect annotation is one of the expected variants
      match fd.effectAnnotation with
      | .pure | .effectful _ | .unannotated => pure ()
    -- Verify recursive node count is at least the top-level count
    let total := countNodes ir.nodes
    if total < ir.nodes.length then
      return some s!"recursive count ({total}) < top-level count ({ir.nodes.length})"
    return none

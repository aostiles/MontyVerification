import MontyVerification

def main (args : List String) : IO Unit := do
  match args.head? with
  | some "--demo" => do
    let path := (args.drop 1).head!
    let content ← IO.FS.readFile path
    match parseIrExportFromString content with
    | .ok ir => runDemo ir
    | .error e => do
      IO.eprintln s!"Parse error: {e}"
      IO.Process.exit 1
  | some "--sanity" => do
    sanityCheckSample
    match (args.drop 1).head? with
    | some dir => do
      IO.println "\n=== Corpus Deep Sanity Check ==="
      let entries ← System.FilePath.readDir dir
      let jsonFiles := entries.filter fun e => e.fileName.endsWith ".json"
      let mut success := 0
      let mut failed := 0
      let mut errors : List (String × String) := []
      for entry in jsonFiles do
        match ← sanityCheckCorpusFile entry.path with
        | none => success := success + 1
        | some e =>
          failed := failed + 1
          errors := errors ++ [(entry.fileName, e)]
      IO.println s!"Total: {success + failed}"
      IO.println s!"Deep traversal OK: {success}"
      IO.println s!"Failed: {failed}"
      if !errors.isEmpty then
        IO.println "\nFailed files:"
        for (name, err) in errors do
          IO.println s!"  {name}: {err}"
    | none => pure ()
  | some "--corpus" => do
    let dir := (args.drop 1).head!
    let entries ← System.FilePath.readDir dir
    let jsonFiles := entries.filter fun e => e.fileName.endsWith ".json"
    let sorted := jsonFiles.toList.mergeSort fun a b => a.fileName < b.fileName
    let mut success := 0
    let mut failed := 0
    let mut errors : List (String × String) := []
    for entry in sorted do
      let content ← IO.FS.readFile entry.path
      match parseIrExportFromString content with
      | .ok _ => success := success + 1
      | .error e =>
        failed := failed + 1
        let firstLine := (e.splitOn "\n").head!
        errors := errors ++ [(entry.fileName, firstLine)]
    IO.println s!"=== Lean Corpus Parse Summary ==="
    IO.println s!"Total: {success + failed}"
    IO.println s!"Success: {success}"
    IO.println s!"Failed: {failed}"
    if !errors.isEmpty then
      IO.println "\nFailed files:"
      for (name, err) in errors do
        IO.println s!"  {name}: {err}"
  | some "--codegen" => do
    let rest := args.drop 1
    let validate := rest.contains "--validate"
    -- `--source <foo.py>` lets the user point at the original Python
    -- file so the codegen can read `# external: <name> <effects>`
    -- directives from comments. If omitted, the codegen tries to
    -- resolve the source from the IR's filename string (which monty
    -- usually populates with a relative path), and if THAT file
    -- exists at the current working directory, reads it. Either way
    -- the directives extend the hardcoded `externalPerms` table.
    let sourceFromFlag : Option String :=
      let idx := rest.findIdx? (· == "--source")
      match idx with
      | some i => (rest.drop (i + 1)).head?
      | none => none
    let fileArgs := rest.filter fun a =>
      a != "--validate" && a != "--source" &&
      (sourceFromFlag.isNone || a != sourceFromFlag.getD "")
    let path := fileArgs.head!
    let outPath := (fileArgs.drop 1).head?
    let content ← IO.FS.readFile path
    match parseIrExportFromString content with
    | .ok ir => do
      -- Try to find a source file to scan for `# external:` directives.
      -- Priority: explicit --source flag, then ir's filename string at
      -- index 10000 (monty's convention). If neither exists, no
      -- directives are loaded — the hardcoded table is the only source.
      let resolveSourcePath : IO (Option String) := do
        match sourceFromFlag with
        | some p => pure (some p)
        | none =>
          -- The IR's first position usually has filename = StringId
          -- pointing to the original source file path. Walk the
          -- IR briefly to find one.
          let pathFromIr := extractFirstFilename ir
          match pathFromIr with
          | none => pure none
          | some p =>
            let pathOk ← (System.FilePath.pathExists p : IO Bool)
            if pathOk then pure (some p) else pure none
      let sourcePath ← resolveSourcePath
      let customExts ← match sourcePath with
        | none => pure []
        | some p => do
          let pyContent ← IO.FS.readFile p
          pure (parseExternalDirectives pyContent)
      if validate then
        -- Validate each declaration through Lean.Syntax before writing.
        let env? ← loadValidationEnv
        match ← generateAndValidateLean ir env? customExts with
        | .ok leanSrc =>
          match outPath with
          | some out => do
            IO.FS.writeFile out leanSrc
            IO.println s!"Generated {out} (validated)"
          | none => IO.print leanSrc
        | .error e => do
          IO.eprintln s!"Syntax validation failed: {e}"
          IO.Process.exit 1
      else
        let leanSrc := generateLean ir customExts
        match outPath with
        | some out => do
          IO.FS.writeFile out leanSrc
          IO.println s!"Generated {out}"
        | none => IO.print leanSrc
    | .error e => do
      IO.eprintln s!"Parse error: {e}"
      IO.Process.exit 1
  | some path => do
    let content ← IO.FS.readFile path
    match parseIrExportFromString content with
    | .ok ir => do
      IO.println s!"Parsed IR successfully!"
      IO.println s!"String table: {ir.stringTable.size} entries"
      IO.println s!"Top-level nodes: {ir.nodes.length}"
      for node in ir.nodes do
        match node with
        | .funcDef fd =>
          let name := ir.resolveString fd.name.nameId
          let effStr := match fd.effectAnnotation with
            | .pure => "Pure"
            | .effectful effs => s!"Effectful({effs.length} effects)"
            | .unannotated => "Unannotated"
          IO.println s!"  FunctionDef '{name}' [{effStr}]"
        | .assign id _ =>
          let name := ir.resolveString id.nameId
          IO.println s!"  Assign '{name}'"
        | .expr _ => IO.println "  Expr"
        | _ => IO.println s!"  (other node)"
    | .error e => do
      IO.eprintln s!"Parse error: {e}"
      IO.Process.exit 1
  | none => do
    IO.eprintln "Usage: montyverification <ir.json>"
    IO.eprintln "       montyverification --demo <ir.json>"
    IO.eprintln "       montyverification --corpus <dir>"
    IO.eprintln "       montyverification --codegen [--validate] <ir.json> [output.lean]"
    IO.eprintln "       montyverification --sanity [corpus_dir]"
    IO.Process.exit 1

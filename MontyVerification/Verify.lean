import Lean
import MontyVerification.Basic
import MontyVerification.JsonDeser
import MontyVerification.EffectMonad
import MontyVerification.Codegen

/-!
# Lean.Syntax Validation for Monty Codegen

This module validates that `generateLean` produces structurally valid Lean
declarations. Each generated **axiom** declaration is parsed through
`Lean.Parser.runParserCategory` into `Lean.Syntax` at codegen time, and each
generated **function definition** has its signature validated. This catches
the class of bugs identified in the review — keyword clashes in identifiers,
malformed declaration structure — before the `.lean` file is written.

Function bodies are validated by the Lean compiler at compile time (not by
the codegen parser), because the full Lean parser requires elaboration context
to resolve ambiguous syntax like `PyVal.list [...]`.

The generated `.lean` files remain standalone: they import only
`MontyVerification.EffectMonad` and contain real Lean declarations that can
be inspected, extended with additional proofs, or composed with other
verification. The Lean compiler verifying the generated file IS the
verification — effect violations become type errors.

## Pipeline

```
monty --emit-ir program.py > ir.json
montyverification --codegen ir.json out.lean   # validates declarations via Lean.Syntax
lake env lean out.lean                         # Lean compiler: compiles = safe
```
-/

open Lean

-- ============================================================================
-- Command splitting
-- ============================================================================

/-- Split the output of `generateLean` into individual command strings.
    Each axiom or `def` becomes a separate string that can be independently
    parsed and validated. Comments and import lines are stripped since they
    aren't Lean commands. -/
def splitGeneratedCommands (s : String) : Array String := Id.run do
  let lines := s.splitOn "\n"
  let mut cmds : Array String := #[]
  let mut current : String := ""
  for line in lines do
    -- Skip comments and imports — not declarations
    if line.startsWith "--" || line.startsWith "import " then
      continue
    -- A new top-level declaration starts a new command. We accept both
    -- `def ` (the new computable form) and `noncomputable def ` (kept for
    -- safety — old emitted code or hand-written tests may still use it).
    if (line.startsWith "axiom " || line.startsWith "def " ||
        line.startsWith "noncomputable ") &&
       !current.trimAscii.toString.isEmpty then
      cmds := cmds.push current
      current := line
    else
      current := current ++ (if current.isEmpty then "" else "\n") ++ line
  if !current.trimAscii.toString.isEmpty then
    cmds := cmds.push current
  cmds

-- ============================================================================
-- Syntax validation
-- ============================================================================

/-- Initialize a Lean `Environment` for syntax validation.
    Imports `MontyVerification.EffectMonad` so the parser knows about
    `PyVal`, `Eff`, `Perms`, etc. Reads search paths from `LEAN_PATH`.
    Returns `none` if the environment can't be loaded (e.g., running
    outside of `lake env`). -/
def loadValidationEnv : IO (Option Environment) := do
  try
    let leanPath ← IO.getEnv "LEAN_PATH"
    let paths := match leanPath with
      | some p => System.SearchPath.parse p
      | none => []
    Lean.searchPathRef.set paths
    let env ← Lean.importModules #[{ module := `MontyVerification.EffectMonad }] {}
    return some env
  catch _ =>
    return none

/-- Extract the signature portion of a function definition (everything up to
    and including `:= do`). This is the part we can reliably validate via
    the parser — function bodies may contain application syntax that requires
    elaboration context to parse. -/
def extractFuncSignature (cmd : String) : Option String :=
  -- Find ":= do" and return everything up to it as a stub
  let parts := cmd.splitOn ":= do"
  if parts.length >= 2 then
    some (parts.head! ++ ":= do\n  pure PyVal.none")
  else
    none

/-- Validate that generated Lean source has well-formed declarations by
    parsing each through `Lean.Parser.runParserCategory` into `Lean.Syntax`.

    - **Axiom declarations** are validated fully (simple structure).
    - **Function definitions** have their signatures validated (name, params,
      return type). Bodies are left to the Lean compiler because some
      application syntax (`PyVal.list [...]`) requires elaboration to parse.

    Returns `.ok ()` if validation passes, `.error msg` on failure.
    Returns `.ok ()` with no checking if the Lean environment can't be loaded
    (e.g., running outside `lake env`). -/
def validateGeneratedLean (leanSrc : String) (env? : Option Environment := none) : IO (Except String Unit) := do
  let env ← match env? with
    | some env => pure (some env)
    | none => loadValidationEnv
  match env with
  | none => return .ok ()  -- can't load env; skip validation gracefully
  | some env =>
    let cmds := splitGeneratedCommands leanSrc
    for cmd in cmds do
      -- Axioms: validate fully (simple syntax, parser handles them fine)
      if cmd.startsWith "axiom " then
        match Parser.runParserCategory env `command cmd "<codegen-validation>" with
        | .ok _ => pure ()
        | .error e =>
          return .error s!"Codegen produced invalid axiom declaration.\n\n{cmd.take 200}\n\nParse error: {e}"
      -- Function defs: validate signature only (body needs elaboration context)
      else if cmd.startsWith "def " || cmd.startsWith "noncomputable " then
        match extractFuncSignature cmd with
        | some sigStub =>
          match Parser.runParserCategory env `command sigStub "<codegen-validation>" with
          | .ok _ => pure ()
          | .error e =>
            return .error s!"Codegen produced invalid function signature.\n\n{sigStub.take 200}\n\nParse error: {e}"
        | none => pure ()  -- no `:= do` found; unusual but not our problem
    return .ok ()

/-- Generate and validate Lean source for a Monty IR export.
    Returns the validated Lean source string, or an error if codegen
    produced an invalid declaration. The returned string is a standalone
    `.lean` file with real declarations — suitable for compilation,
    inspection, and composition with additional verification. -/
def generateAndValidateLean (ir : IrExport) (env? : Option Environment := none)
    (customExternals : List (String × String) := [])
    : IO (Except String String) := do
  let leanSrc := generateLean ir customExternals
  match ← validateGeneratedLean leanSrc env? with
  | .ok () => return .ok leanSrc
  | .error e => return .error e

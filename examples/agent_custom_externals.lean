-- Properties for examples/agent_custom_externals.py
--
-- Demonstrates the source-level `# external: <name> <effects>`
-- directive mechanism. The four externals here (`read_secret`,
-- `fetch_invoice`, `charge_card`, `write_audit_log`) are NOT in
-- the hardcoded `externalPerms` table — they're declared at the
-- top of the Python file via directive comments. The codegen
-- reads the Python file, parses the directives, and treats each
-- one as having the user-declared effect set.
--
-- Verification value: a deployer with their own tool API can
-- type-verify LLM code against it without modifying the
-- MontyVerification source.

/-! ## Inferred effect type

The function calls four externals at four different effect levels:
  - read_secret  → env
  - fetch_invoice → net
  - charge_card  → net
  - write_audit_log → fs

The inferred type is the precise union — `{ net, fs, env }`. -/

example :
    (process_invoice : PyVal → Eff { env := true, net := true, fs := true } PyVal)
      = process_invoice := rfl

/-! ## Each external has the declared concrete type

These witness that the directives parsed correctly. If the codegen
had ignored a directive, the corresponding external would be at
`Perms.top` instead. -/

example :
    (ext_read_secret : PyVal → Eff { env := true } PyVal) = ext_read_secret := rfl

example :
    (ext_fetch_invoice : PyVal → Eff { net := true } PyVal) = ext_fetch_invoice := rfl

example :
    (ext_charge_card : PyVal → PyVal → Eff { net := true } PyVal) = ext_charge_card := rfl

example :
    (ext_write_audit_log : PyVal → Eff { fs := true } PyVal) = ext_write_audit_log := rfl

/-! ## Symbolic execution: ordering invariants over the tool calls

A compliance/security story: prove that every charge is preceded
by a secret read AND followed by an audit log. The user only
declared the externals — they did NOT have to write any
hand-coded Lean reference for the workflow. -/

example :
    EffAST.calledBefore "ext_read_secret" "ext_charge_card"
        process_invoice__ast = true := by
  native_decide

example :
    EffAST.calledBefore "ext_charge_card" "ext_write_audit_log"
        process_invoice__ast = true := by
  native_decide

/-- Sanity: reverse direction is FALSE. -/
example :
    EffAST.calledBefore "ext_write_audit_log" "ext_charge_card"
        process_invoice__ast = false := by
  native_decide

/-- Every reachable return path writes an audit log. -/
example :
    EffAST.eventuallyCalls "ext_write_audit_log" process_invoice__ast = true := by
  native_decide

/-- Every reachable return path reads a secret exactly once. -/
example :
    EffAST.calledExactlyOnce "ext_read_secret" process_invoice__ast = true := by
  native_decide

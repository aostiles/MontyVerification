-- Properties for examples/agent_protocol_check.py

/-! ## Type-level: each role has exactly its declared effect set

These four `def` declarations are the entire protocol verification.
Lean accepted the file, so each function has the type its annotation
claims. The fact that the file COMPILED is the proof. -/

/-- `summarize_text` is `Pure[str]` — `Perms.none` means it touches
    no externals. If the body called `send_email` or `write_file`,
    Lean would reject the `Eff Perms.none` annotation at compile. -/
example :
    (summarize_text : PyVal → PyVal → Eff Perms.none PyVal) = summarize_text := rfl

/-- `notify_user` is `Effect[Net, str]` — `{ net := true }` carries
    only the network effect. A body that touched `write_file` (an
    `FS` external) would fail to type-check at the call site, since
    `Perms.sub { fs := true } { net := true }` is decidably false. -/
example :
    (notify_user : PyVal → PyVal → Eff { net := true } PyVal) = notify_user := rfl

/-- `audit_log` is `Effect[FS, str]` — `{ fs := true }` carries only
    the filesystem effect. Symmetric to `notify_user`. -/
example :
    (audit_log : PyVal → Eff { fs := true } PyVal) = audit_log := rfl

/-! ## The externals themselves are typed correctly

Codegen pinned `send_email` to `Net` and `write_file` to `FS` from
its hardcoded externals table. The `def`s exist, so the externals
have those types. -/

example :
    (ext_send_email : PyVal → PyVal → Eff { net := true } PyVal) = ext_send_email := rfl
example :
    (ext_write_file : PyVal → PyVal → Eff { fs := true } PyVal) = ext_write_file := rfl

/-! ## Cross-role separation: the perm sets are non-comparable

Net cannot be lifted into FS, and vice versa. This is what makes the
role separation real: a `Net` function can't sneak in an FS call
(and vice versa) because the perms relation refuses to lift between
disjoint effect sets. -/

example : ¬ Perms.sub { net := true } { fs := true } := by decide
example : ¬ Perms.sub { fs := true } { net := true } := by decide

/-- Both effect sets are sub-sets of `Perms.top`. A function that
    needs both would have to declare `Perms.top` (or `{ net := true,
    fs := true }`). -/
example : Perms.sub { net := true } Perms.top := by decide
example : Perms.sub { fs := true } Perms.top := by decide

/-! ## Pure helper reduces to its documented value -/

example :
    (summarize_text (PyVal.str "hello world") (PyVal.int 5)).run
      = .ok (PyVal.str "hello") := by native_decide

example :
    (summarize_text (PyVal.str "hi") (PyVal.int 100)).run
      = .ok (PyVal.str "hi") := by native_decide

/-! ## Module-level execution

Every assertion in the source passes when the module body runs.
The Net/FS externals stub to `PyVal.none` in our model, but the
return values of `notify_user` and `audit_log` are concrete
literals (`'sent'` / `'logged'`) chosen by the agent. -/

example : («__module__».run = .ok PyVal.none) := by native_decide

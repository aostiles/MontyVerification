-- Properties for examples/agent_custom_effects.py
--
-- Custom effects beyond net/fs/env/time. The codegen extends
-- `Perms` with a `custom : List String` field, and the directive
-- system maps unknown effect names into it.

/-! ## Inferred effect types -/

example :
    (lookup_user : PyVal → Eff { custom := ["db"] } PyVal) = lookup_user := rfl

example :
    (record_action : PyVal → PyVal → Eff { custom := ["audit"] } PyVal)
      = record_action := rfl

/-- The composite function gets the union of every reached effect,
    including the standard `net` and the custom `db` and `audit`.
    The custom list is sorted alphabetically by codegen convention. -/
example :
    (notify_and_audit : PyVal → PyVal → Eff { net := true, custom := ["audit", "db"] } PyVal)
      = notify_and_audit := rfl

/-! ## Sub-permission witnesses for custom effects

The same `Perms.sub` machinery handles the standard effects and
the custom names. A function declared as `{ custom := ["db"] }`
is a subset of `{ custom := ["db", "audit"] }` (additive). -/

example : Perms.sub { custom := ["db"] } { custom := ["audit", "db"] } := by decide

example : Perms.sub Perms.none { custom := ["db"] } := by decide

example : ¬ Perms.sub { custom := ["db"] } Perms.none := by decide

/-- `Perms.top` absorbs every custom effect — that's the
    `customSubset` rule in the sub relation. -/
example : Perms.sub { custom := ["db", "gpu", "anything"] } Perms.top := by decide

/-! ## First-class call graph queries

The codegen also emits a `call_graph : CallGraph` value listing
every function and its direct callees. User property files can
query it directly. -/

example :
    CallGraph.callees call_graph "notify_and_audit"
      = ["lookup_user", "ext_send_email", "record_action"] := by
  native_decide

/-- `notify_and_audit` transitively reaches `ext_query_db` (via
    `lookup_user`). -/
example :
    CallGraph.reaches call_graph "notify_and_audit" "ext_query_db" = true := by
  native_decide

/-- `notify_and_audit` transitively reaches `ext_write_audit` (via
    `record_action`). -/
example :
    CallGraph.reaches call_graph "notify_and_audit" "ext_write_audit" = true := by
  native_decide

/-- `lookup_user` does NOT reach `ext_send_email` (it's a leaf
    that only calls `ext_query_db`). -/
example :
    CallGraph.neverReaches call_graph "lookup_user" "ext_send_email" = true := by
  native_decide

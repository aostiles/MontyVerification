-- Properties for examples/agent_interprocedural_bug.py
--
-- A trading system with a bug: `fast_execute` skips input
-- validation. The interprocedural analysis catches it —
-- there exists a path through `process_trade` where
-- `execute_trade` runs without a preceding `validate_input`.

def trade_locals : List (String × EffAST) :=
  [ ("slow_execute", slow_execute__ast)
  , ("fast_execute", fast_execute__ast)
  , ("audit_and_notify", audit_and_notify__ast)
  ]

/-! ## The slow path is correct

`slow_execute` validates before executing. -/

example :
    EffAST.calledBefore "ext_validate_input" "ext_execute_trade"
        slow_execute__ast = true := by
  native_decide

/-! ## The fast path has the bug

`fast_execute` does NOT call `validate_input` at all. -/

example :
    EffAST.eventuallyCalls "ext_validate_input" fast_execute__ast = false := by
  native_decide

/-! ## Interprocedural: the bug surfaces in `process_trade`

Because `process_trade` branches — one branch calls `fast_execute`
(which skips validation) and the other calls `slow_execute` (which
validates) — the interprocedural analysis intersects the must-sets
across both branches. The fast branch's must-set has no
`validate_input`, so the intersection is empty, and the ordering
invariant FAILS. -/

/-- validate_input is NOT guaranteed before execute_trade. -/
example :
    EffAST.calledBeforeInter "ext_validate_input" "ext_execute_trade"
        trade_locals process_trade__ast = false := by
  native_decide

/-! ## But authentication and auditing are still sound

These invariants hold on BOTH branches — the bug is specifically
in the validation gate, not the rest of the compliance flow. -/

/-- Authentication happens before any trade execution. -/
example :
    EffAST.calledBeforeInter "ext_authenticate" "ext_execute_trade"
        trade_locals process_trade__ast = true := by
  native_decide

/-- Every path audits the trade. -/
example :
    EffAST.calledBeforeInter "ext_execute_trade" "ext_record_audit"
        trade_locals process_trade__ast = true := by
  native_decide

/-- Every path notifies compliance. -/
example :
    EffAST.calledBeforeInter "ext_record_audit" "ext_notify_compliance"
        trade_locals process_trade__ast = true := by
  native_decide

/-- End-to-end: authenticate before notify (spans all helpers). -/
example :
    EffAST.calledBeforeInter "ext_authenticate" "ext_notify_compliance"
        trade_locals process_trade__ast = true := by
  native_decide

/-! ## Exactly-once guarantees on the audit path -/

example :
    EffAST.calledExactlyOnce "ext_record_audit" audit_and_notify__ast = true := by
  native_decide

example :
    EffAST.calledExactlyOnce "ext_notify_compliance" audit_and_notify__ast = true := by
  native_decide

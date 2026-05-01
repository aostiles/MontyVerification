-- Properties for examples/agent_property_zoo.py
--
-- Demonstrates four symbolic-execution properties on the ETL agent:
--   - calledExactlyOnce target
--   - mutuallyExclusive a b
--   - calledAfter a b
--   - eventuallyCalls target
--
-- The ETL body:
--   open_source  → read_data → (maybe check_invariants) →
--   write_destination → close_source → log_completion

/-! ## calledBefore — every reachable call to b is preceded by a -/

example :
    EffAST.calledBefore "ext_open_source" "ext_read_data" run_etl__ast = true := by
  native_decide

example :
    EffAST.calledBefore "ext_read_data" "ext_write_destination" run_etl__ast = true := by
  native_decide

example :
    EffAST.calledBefore "ext_write_destination" "ext_close_source" run_etl__ast = true := by
  native_decide

/-! ## eventuallyCalls — every return path calls target

The four externals NOT inside the conditional `if validate:` are
called on every path. `check_invariants` is only called on one of
the two branches, so it's NOT eventually-called. -/

example :
    EffAST.eventuallyCalls "ext_open_source" run_etl__ast = true := by
  native_decide

example :
    EffAST.eventuallyCalls "ext_close_source" run_etl__ast = true := by
  native_decide

example :
    EffAST.eventuallyCalls "ext_log_completion" run_etl__ast = true := by
  native_decide

/-- `check_invariants` is conditional — NOT every path calls it. -/
example :
    EffAST.eventuallyCalls "ext_check_invariants" run_etl__ast = false := by
  native_decide

/-! ## calledExactlyOnce — count = 1 on every reachable path

The unconditional externals are called exactly once. We don't have
a mal-shape demonstrating "called twice" because the body is
linear, but the tests below witness the analysis is alive. -/

example :
    EffAST.calledExactlyOnce "ext_open_source" run_etl__ast = true := by
  native_decide

example :
    EffAST.calledExactlyOnce "ext_log_completion" run_etl__ast = true := by
  native_decide

/-- `check_invariants` is called once on the validate-branch and
    zero times on the other. The branches don't agree, so
    "exactly once on every path" is FALSE. -/
example :
    EffAST.calledExactlyOnce "ext_check_invariants" run_etl__ast = false := by
  native_decide

/-! ## calledAfter — every call to a is followed by b on every path

`open_source` is always followed by `close_source`. -/

example :
    EffAST.calledAfter "ext_open_source" "ext_close_source" run_etl__ast = true := by
  native_decide

/-- `read_data` is always followed by `write_destination`. -/
example :
    EffAST.calledAfter "ext_read_data" "ext_write_destination" run_etl__ast = true := by
  native_decide

/-! ## mutuallyExclusive — no path calls both

This is a sanity check — `open_source` and `close_source` are BOTH
called, so they are NOT mutually exclusive. The proof witnesses
the negative direction of the analysis. -/

example :
    EffAST.mutuallyExclusive "ext_open_source" "ext_close_source" run_etl__ast = false := by
  native_decide

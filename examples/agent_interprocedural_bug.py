# call-external
# external: authenticate net
# external: validate_input net
# external: execute_trade net
# external: record_audit fs
# external: notify_compliance net
"""Interprocedural bug detection: a helper skips a required step.

A trading system where compliance requires that every trade is
authenticated, validated, audited, and reported. The bug: the
`fast_execute` helper skips `validate_input`, and the main
`process_trade` function uses it on the fast path.

The matching `.lean` proves:
  - The slow path correctly validates before executing.
  - The fast path does NOT validate before executing (the bug).
  - Both paths audit and notify (the compliance guarantee still
    holds for those steps).
"""


def slow_execute(order, creds):
    validate_input(order)
    return execute_trade(order, creds)


def fast_execute(order, creds):
    return execute_trade(order, creds)


def audit_and_notify(trade_id, result):
    record_audit(trade_id, result)
    notify_compliance(trade_id)


def process_trade(order, creds, use_fast_path):
    token = authenticate(creds)
    if use_fast_path:
        result = fast_execute(order, token)
    else:
        result = slow_execute(order, token)
    audit_and_notify(order, result)
    return result

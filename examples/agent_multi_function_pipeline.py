# call-external
"""Interprocedural symbolic execution: pipeline split across helpers.

This is the realistic shape: an agent's pipeline isn't a single
function, it's a main entry point that calls helper functions, each
of which calls one or more tools. The ordering invariant we want to
verify is "request_approval before process_payment before
log_transaction" — but each step lives in its own helper.

The matching `.lean` builds a `locals` table mapping each helper's
name to its emitted `EffAST`, and uses
`EffAST.calledBeforeInter` to walk `execute_payment__ast` while
inlining the helpers' bodies at the call sites.
"""


def request_step(payment, approver):
    return request_approval(payment, approver)


def process_step(payment, approval):
    return process_payment(payment, approval)


def log_step(payment, receipt):
    log_transaction(payment, receipt)
    return receipt


def execute_payment(payment, approver):
    approval = request_step(payment, approver)
    receipt = process_step(payment, approval)
    log_step(payment, receipt)
    return receipt

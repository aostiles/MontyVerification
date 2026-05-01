# call-external
"""Companion to agent_payment_workflow.py: a *buggy* agent that the
symbolic-execution analysis catches.

The bug: the cached-payment fast path skips `request_approval`. The
agent author thought "if the payment is cached we already approved it
once, no need to ask again" — except the data flow they relied on
isn't part of the verification trust boundary, so the codegen sees a
path from entry to `process_payment` that doesn't go through
`request_approval`, and the ordering theorem fails.

The matching `.lean` proves the BUG with `= false` — i.e. the
analysis correctly reports that the ordering invariant does NOT hold
on every path. If a future codegen change accidentally caused the
analysis to over-approximate (reporting `= true` here), the
regression would catch it.
"""


def execute_payment(payment, approver, is_cached):
    if is_cached:
        # BUG: cached path skips approval.
        receipt = process_payment(payment, payment)
    else:
        approval = request_approval(payment, approver)
        receipt = process_payment(payment, approval)
    log_transaction(payment, receipt)
    return receipt

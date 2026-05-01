# call-external
"""Negative example: agent has the buggy reordering AND tries to
prove the wrong-direction ordering invariant.

The Python source has the same bug as `agent_payment_buggy.py` —
the cached fast path skips approval. The matching `.lean` claims
"request_approval is called before process_payment on every path",
which is FALSE (the cached path skips approval). The example
should FAIL to compile because the `native_decide` of `= true`
discharges to `false`.

This is the load-bearing test that the symbolic-execution layer
is sound in the negative direction: a wrong claim about ordering
must be rejected by Lean.
"""


def execute_payment(payment, approver, is_cached):
    if is_cached:
        receipt = process_payment(payment, payment)
    else:
        approval = request_approval(payment, approver)
        receipt = process_payment(payment, approval)
    log_transaction(payment, receipt)
    return receipt

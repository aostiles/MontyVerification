# call-external
"""Symbolic-execution demo: ordering invariants without annotations.

The compliance story: legal flagged the payment processor — every
`process_payment` call must be preceded by a `request_approval` call,
and every transaction must be logged. The agent code itself is plain
Python with no Pure[]/Effect[] annotations and no parallel typed
witness layer. The verification operates over the codegen-emitted
`EffAST` representation of the function body.

The matching `.lean` file proves three ordering theorems by
`native_decide`:

  1. request_approval is called before process_payment on every path.
  2. request_approval is called before log_transaction on every path.
  3. process_payment is called before log_transaction on every path.

And one negation theorem (proving the analysis catches the wrong
direction):

  4. log_transaction is NOT called before process_payment.

The decision procedure walks the function's `EffAST` value (a
defunctionalized free monad emitted alongside the executable `def`)
and answers each ordering question by forward dataflow over the call
sequence. Branches and try/except are exposed as structural
constructors so the analysis covers both arms.

This is the core verification story for code-mode agents:
*ordering* invariants on tool calls, expressible without modifying
the source language, decided mechanically by Lean's evaluator.
"""


def execute_payment(payment, approver):
    """The agent body. The Python source has no annotations — the
    codegen extracts the call sequence from the body and emits an
    `execute_payment__ast : EffAST` value alongside the executable
    `def execute_payment`."""
    approval = request_approval(payment, approver)
    receipt = process_payment(payment, approval)
    log_transaction(payment, receipt)
    return receipt

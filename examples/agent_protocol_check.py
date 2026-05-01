"""Realistic code-mode-style agent: protocol property — only the
declared tools are reachable.

This example exists to demonstrate the *negative space* of effect
tracking: a function annotated with a specific effect set can ONLY
reach externals in that set. The annotations are decided at
compile time by Lean's type checker, so the verification is the
fact that the file compiles.

The agent here has three roles:
  - `summarize_text` is `Pure[str]` — pure string manipulation only.
  - `notify_user` is `Effect[Net, str]` — sends an email and
    returns a confirmation.
  - `audit_log` is `Effect[FS, str]` — writes to the filesystem.

Each role's TYPE is the proof obligation. If the LLM had written
any of these the wrong way (e.g. tried to `read_file` from
`notify_user`), Lean would refuse to compile the file. The
verification surface lets the deployer trust an LLM's *plan*
because the plan can no longer lie about what tools it'll use.
"""


def summarize_text(text: str, limit: int) -> Pure[str]:
    """Pure: trims text. Cannot touch any external."""
    return text[:limit]


def notify_user(recipient: str, message: str) -> Effect[Net, str]:
    """Net: sends an email and returns a confirmation token. Cannot
    touch the filesystem."""
    send_email(recipient, message)
    return 'sent'


def audit_log(action: str) -> Effect[FS, str]:
    """FS: writes to the audit log. Cannot touch the network."""
    write_file('/tmp/audit.log', action)
    return 'logged'


# Pure helper assertions. We deliberately do NOT call `notify_user`
# or `audit_log` from module-level code: the module body has no
# effect annotation (it's `Pure` by default), so calling an effectful
# helper would be a TYPE ERROR. The verification of the role
# functions is at the type level — they exist with their declared
# annotations because the file compiles.
assert summarize_text('hello world', 5) == 'hello', 'summarize_text bounds'
assert summarize_text('hi', 100) == 'hi', 'summarize_text passthrough'
assert summarize_text('', 10) == '', 'summarize_text empty'

# external: ext_log_msg net
"""Regression test for G4: a Python source containing the literal
sequence `← (` shouldn't get its contents corrupted by the codegen's
bind-wrap rewriting.

Before the G4 fix, the codegen used a global string replace
`bodyStr.replace "← (" "← Eff.liftSub ("` that would silently
rewrite occurrences of the sequence inside generated string
literals. After the fix, the rewriter is string-literal-aware and
skips them.

The function below has `Net` perms (so the wrap rewriting fires)
and contains a string literal with the corrupting sequence. If
G4 ever regresses, this file will fail to compile or the assert
about the string value will be wrong.
"""


def log_message(name):
    msg = '← (received from ' + name + ')'
    ext_log_msg(msg)
    return msg

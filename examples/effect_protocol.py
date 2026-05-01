# call-external
"""Effect-tracking demo. `pure_helper` declares `Pure[int]` and
contains no externals; `net_caller` declares `Effect[Net, int]` and
calls a `Net` external. The codegen now uses `Eff.liftSub` to wrap
the bind of `pure_helper(x)` inside `net_caller`, so the sub-permission
relationship is checked by `decide`. If you swapped the annotations
the file would not compile — that's the soundness story."""


def pure_helper(x: int) -> Pure[int]:
    return x * 2


def net_caller(x: int) -> Effect[Net, int]:
    doubled = pure_helper(x)
    notified = ext_notify(doubled)
    return doubled


# Direct test of the pure helper (no externals).
assert pure_helper(21) == 42, 'pure helper doubles its input'
assert pure_helper(0) == 0, 'pure helper preserves zero'

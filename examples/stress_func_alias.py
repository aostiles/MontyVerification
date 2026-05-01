# external: ext_send_email net
"""Stress test: function aliasing precision (P4 fix).

`f = some_known_func` followed by `f(x)` should dispatch to
`some_known_func` directly, not via `PyVal.callFn` (which would
widen the surrounding function to `Perms.top`).
"""


def send_alert(message):
    ext_send_email(message)
    return message


def main():
    # Aliasing a known local function. The codegen should
    # dispatch `notify(...)` to `send_alert(...)` directly.
    notify = send_alert
    notify('hello')
    return 0

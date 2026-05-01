-- Properties for examples/stress_func_alias.py
-- Function aliasing precision (P4 fix).

/-- `send_alert` is inferred as `Net` (it calls `ext_ext_send_email`). -/
example : (send_alert : PyVal → Eff { net := true } PyVal) = send_alert := rfl

/-- `py_main` aliases `send_alert` and calls it. With the alias
    resolution in effect inference, py_main inherits send_alert's
    `Net` perms — without the fix it would either be at `Perms.none`
    (and fail to compile) or get widened to `Perms.top` (coarse). -/
example : (py_main : Eff { net := true } PyVal) = py_main := rfl

-- Properties for examples/agent_async_orchestrator.py
--
-- Pure async coroutines composed via asyncio.gather. Every
-- coroutine body is pure arithmetic or string concatenation,
-- so the entire module reduces computationally in Lean's kernel.

/-! ## Each coroutine is pure (Perms.none) -/

example :
    (double : PyVal → Eff Perms.none (PyClosure Perms.none 0)) = double := rfl

example :
    (add_ten : PyVal → Eff Perms.none (PyClosure Perms.none 0)) = add_ten := rfl

example :
    (greet : PyVal → Eff Perms.none (PyClosure Perms.none 0)) = greet := rfl

/-! ## The module body reduces: gather(double(3), add_ten(5), greet("world"))

`interpWithCalls` actually calls the coroutine bodies (not stubs),
so the gather chain reduces to `[6, 15, "hello world"]` and the
assert passes. -/

example : «__module__eval».run = .ok PyVal.none := by native_decide

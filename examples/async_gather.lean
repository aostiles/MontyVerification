-- Properties for examples/async_gather.py

/-- The module body with cross-function call resolution: gather
    constructs `[1, 2, 3]` from the task results, and the assertion
    `result == [1, 2, 3]` passes. -/
example : «__module__eval».run = .ok PyVal.none := by native_decide

/-- Each `async def` lowers as a coroutine constructor returning a
    `PyClosure 0` thunk. The type-level witness: the `def` exists
    with the expected signature. -/
example :
    (task1 : Eff Perms.none (PyClosure Perms.none 0)) = task1 := rfl
example :
    (task2 : Eff Perms.none (PyClosure Perms.none 0)) = task2 := rfl
example :
    (task3 : Eff Perms.none (PyClosure Perms.none 0)) = task3 := rfl

/-- The whole `gather`-then-`await` chain reduces — at the value level,
    not just the type level — to the expected list. We replay it here
    against the generated tasks to give a direct value-equality
    witness independent of the module body. -/
example :
    (Eff.runFunction (do
      let _coro0 ← task1
      let _res0 ← PyClosure.call0 _coro0
      let _coro1 ← task2
      let _res1 ← PyClosure.call0 _coro1
      let _coro2 ← task3
      let _res2 ← PyClosure.call0 _coro2
      (Eff.return (PyVal.list [_res0, _res1, _res2]) : Eff Perms.none PyVal))).run
      = .ok (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]) := by
  native_decide

/-- The whole gather chain stays at `Perms.none` — none of the
    coroutines need elevated effects, so the surrounding context is
    pure. If any task had used a `Net` external, the type would have
    been `Eff { net := true }` and this `def` would not type-check. -/
example :
    let prog : Eff Perms.none PyVal := Eff.runFunction (do
      let c1 ← task1
      let r1 ← PyClosure.call0 c1
      let c2 ← task2
      let r2 ← PyClosure.call0 c2
      let c3 ← task3
      let r3 ← PyClosure.call0 c3
      (Eff.return (PyVal.list [r1, r2, r3]) : Eff Perms.none PyVal))
    prog.run = .ok (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]) := by
  native_decide

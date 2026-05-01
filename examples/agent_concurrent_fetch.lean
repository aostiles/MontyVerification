-- Properties for examples/agent_concurrent_fetch.py

/-! ## Type-level: each async fetch is a 0-arg coroutine constructor

The codegen lowers `async def fetch_X` as a function that returns
a `PyClosure 0` thunk (Extension B). Calling `fetch_X` builds the
thunk; awaiting it (via `PyClosure.call0`) runs the body. -/

example :
    (fetch_user : Eff Perms.none (PyClosure Perms.none 0)) = fetch_user := rfl
example :
    (fetch_post_count : Eff Perms.none (PyClosure Perms.none 0)) = fetch_post_count := rfl
example :
    (fetch_likes : Eff Perms.none (PyClosure Perms.none 0)) = fetch_likes := rfl

/-! ## Value-level: each fetch produces the documented payload -/

/-- `fetch_user` thunk runs to `'alice'`. -/
example :
    (fetch_user.bind PyClosure.call0).run = .ok (PyVal.str "alice") := by
  native_decide

example :
    (fetch_post_count.bind PyClosure.call0).run = .ok (PyVal.int 7) := by
  native_decide

example :
    (fetch_likes.bind PyClosure.call0).run = .ok (PyVal.int 42) := by
  native_decide

/-! ## End-to-end: the gather chain assembles the right list

This is the central guarantee for the agent: `asyncio.gather` of N
coroutines produces a list of exactly N results in argument order.
We replay the gather chain as Lean would emit it from the source. -/

/-- The full fan-out fetch reduces to `[user, post_count, likes]`
    with the exact payloads. -/
example :
    (Eff.runFunction (do
      let _coro0 ← fetch_user
      let _res0 ← PyClosure.call0 _coro0
      let _coro1 ← fetch_post_count
      let _res1 ← PyClosure.call0 _coro1
      let _coro2 ← fetch_likes
      let _res2 ← PyClosure.call0 _coro2
      (Eff.return (PyVal.list [_res0, _res1, _res2])
        : Eff Perms.none PyVal))).run
      = .ok (PyVal.list [PyVal.str "alice", PyVal.int 7, PyVal.int 42]) := by
  native_decide

/-- Length is exactly 3 — the agent's "I asked for three fields and
    got three back" invariant. -/
example :
    (Eff.runFunction (do
      let _coro0 ← fetch_user
      let _res0 ← PyClosure.call0 _coro0
      let _coro1 ← fetch_post_count
      let _res1 ← PyClosure.call0 _coro1
      let _coro2 ← fetch_likes
      let _res2 ← PyClosure.call0 _coro2
      (Eff.return (pyLen (PyVal.list [_res0, _res1, _res2]))
        : Eff Perms.none PyVal))).run
      = .ok (PyVal.int 3) := by native_decide

/-- The module body with cross-function call resolution: gather
    constructs the results list, and all four assertions pass. -/
example : «__module__eval».run = .ok PyVal.none := by native_decide

/-! ## Effect-tracking witnesses

The whole gather chain is `Eff Perms.none` because every coroutine
is a `PyClosure Perms.none 0`. If any of the fetches were `Net`,
the chain would be at `Eff { net := true }` and any caller would
have to accept that. -/

example :
    let prog : Eff Perms.none PyVal := Eff.runFunction (do
      let c1 ← fetch_user
      let r1 ← PyClosure.call0 c1
      let c2 ← fetch_post_count
      let r2 ← PyClosure.call0 c2
      let c3 ← fetch_likes
      let r3 ← PyClosure.call0 c3
      (Eff.return (PyVal.list [r1, r2, r3]) : Eff Perms.none PyVal))
    prog.run = .ok (PyVal.list [PyVal.str "alice", PyVal.int 7, PyVal.int 42]) := by
  native_decide

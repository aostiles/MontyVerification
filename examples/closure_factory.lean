-- Properties for examples/closure_factory.py
--
-- The driver script concatenates this file with the codegen output of
-- closure_factory.py and runs the combined file through `lean`. Names
-- like `make_adder`, `add5`, and `«__module__»` are defined by the
-- generated portion above this point.

/-- The whole module runs to completion: every assert in the source
    passes, so `«__module__».run` reduces to `.ok PyVal.none`. -/
example : («__module__».run = .ok PyVal.none) := by native_decide

/-- `make_adder` is a closure factory: its inferred type is
    `Eff Perms.none (PyClosure Perms.none 1)`. The `def` exists,
    which is the type-level witness that codegen lowered the `return
    add` shape to a typed `PyClosure` value (Path 1). -/
example : (make_adder : PyVal → Eff Perms.none (PyClosure Perms.none 1))
    = make_adder := rfl

/-- `make_adder(5)` reduces to a closure that, when called with `3`,
    produces `8`. This is the value-level witness: the captured `x = 5`
    flows through the `PyClosure.call1` dispatch. -/
example :
    ((make_adder (PyVal.int 5)).bind (fun cb => PyClosure.call1 cb (PyVal.int 3))).run
      = .ok (PyVal.int 8) := by native_decide

/-- Two factory invocations produce independent closures with their
    own captured values. -/
example :
    (do
      let cb5  ← make_adder (PyVal.int 5)
      let cb10 ← make_adder (PyVal.int 10)
      let r5  ← PyClosure.call1 cb5  (PyVal.int 100)
      let r10 ← PyClosure.call1 cb10 (PyVal.int 100)
      pure (PyVal.tuple [r5, r10]) : Eff Perms.none PyVal).run
      = .ok (PyVal.tuple [PyVal.int 105, PyVal.int 110]) := by native_decide

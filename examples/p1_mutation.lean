-- Properties for examples/p1_mutation.py
--
-- Demonstrates P1 mutation model: augmented assignment, dict/list
-- subscript set, and state-threaded for-loops (pyForFold).

/-! ## Augmented assignment -/

/-- `counter_demo` uses `x += 3; x += 7`. The codegen applies the
    operator and rebinds, so x = 0 + 3 + 7 = 10. -/
example : counter_demo.run = .ok (PyVal.int 10) := by native_decide

/-! ## Dict subscript set -/

/-- `dict_demo` builds a dict with `d['a'] = 1; d['b'] = 2`.
    The model now correctly tracks subscript assignment. -/
example : dict_demo.run = .ok (PyVal.dict [(PyVal.str "a", PyVal.int 1), (PyVal.str "b", PyVal.int 2)]) := by native_decide

/-! ## List subscript set -/

/-- `list_set_demo` sets `lst[1] = 99`. The model correctly updates
    the element at index 1. -/
example : list_set_demo.run = .ok (PyVal.list [PyVal.int 10, PyVal.int 99, PyVal.int 30]) := by native_decide

/-! ## Mutation inside for-loop (pyForFold) -/

/-- `append_in_loop` builds `[1, 2, 3]` by appending in a for-loop.
    This is the key P1 demo: the codegen detects that `results` is
    mutated via `.append` inside the loop and emits `pyForFold` to
    thread it as accumulator state. -/
example : append_in_loop.run = .ok (PyVal.list [PyVal.int 1, PyVal.int 2, PyVal.int 3]) := by native_decide

/-! ## opAssign inside for-loop -/

/-- `accumulate_sum` computes `10 + 20 + 30 = 60` via `total += x`
    inside a for-loop. The fold threads `total` as accumulator. -/
example : accumulate_sum.run = .ok (PyVal.int 60) := by native_decide

/-! ## Module body runs without error -/

/-- No module-level assertions; just the docstring. -/
example : (∃ v, «__module__».run = .ok v) := ⟨_, rfl⟩

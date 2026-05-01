# call-external
"""P1 mutation model demo: augmented assignment, dict/list subscript
set, and state-threaded for-loops.

Prior to P1, all Python values were immutable in the model. This
file demonstrates that the codegen now correctly models:
  - `counter += 1` (augmented assignment applies the operator)
  - `d[k] = v` (dict subscript set, SSA rebinding)
  - `results.append(x)` inside for-loops (state-threaded fold)
"""


def counter_demo():
    x = 0
    x += 3
    x += 7
    assert x == 10
    return x


def dict_demo():
    d = {}
    d['a'] = 1
    d['b'] = 2
    assert len(d) == 2
    return d


def list_set_demo():
    lst = [10, 20, 30]
    lst[1] = 99
    assert lst[1] == 99
    return lst


def append_in_loop():
    """The key P1 demo: mutation inside a for-loop via pyForFold."""
    results = []
    items = [1, 2, 3]
    for x in items:
        results.append(x)
    assert len(results) == 3
    return results


def accumulate_sum():
    """opAssign inside a for-loop."""
    total = 0
    for x in [10, 20, 30]:
        total += x
    assert total == 60
    return total

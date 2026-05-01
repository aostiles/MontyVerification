"""Closure factory: a function that returns an inner function which
captures the outer parameter. Path 1 of MontyVerification's closure-type
tracking lowers `make_adder` as `Eff Perms.none (PyClosure Perms.none 1)`,
so call sites dispatch via `PyClosure.call1` and the captured value flows
through the type system."""


def make_adder(x):
    def add(y):
        return x + y

    return add


add5 = make_adder(5)
add10 = make_adder(10)

assert add5(3) == 8, 'add5(3) should be 8'
assert add10(3) == 13, 'add10(3) should be 13'
assert add5(0) == 5, 'add5(0) should be 5'

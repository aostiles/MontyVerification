# run-async
"""asyncio.gather of multiple async functions. Extension B lowers
each `async def` as a `PyClosure 0` thunk that closes over its
parameters; Extension A unfolds `asyncio.gather(c1, c2, ...)` into a
sequence of coroutine binds + `PyClosure.call0`s, then collects the
results into a list. The whole chain reduces to a concrete
`PyVal.list` so the assertion verifies by computation."""

import asyncio


async def task1():
    return 1


async def task2():
    return 2


async def task3():
    return 3


result = await asyncio.gather(task1(), task2(), task3())  # pyright: ignore
assert result == [1, 2, 3], 'gather should return results in order'

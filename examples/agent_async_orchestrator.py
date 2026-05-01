# run-async
"""Async coroutines with gather — computational verification.

Pure async tasks whose bodies reduce in Lean's kernel. The
`asyncio.gather` call composes three coroutines and collects
their results into a list. The matching `.lean` proves that
the gathered result is exactly `[6, 15, "hello world"]` by
running the EffProg interpreter via `native_decide`.
"""

import asyncio


async def double(x):
    return x * 2


async def add_ten(x):
    return x + 10


async def greet(name):
    return "hello " + name


result = await asyncio.gather(double(3), add_ten(5), greet("world"))  # pyright: ignore
assert result == [6, 15, "hello world"], 'gather returns results in order'

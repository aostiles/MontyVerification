# call-external
"""Stress test 6: async pipeline with gather.

Multi-coroutine fanout via asyncio.gather, then post-processing the
results. Exercises async function emission + listcomp containing
closure-returning call (the case fixed by the
`allowClosureReturn` context flag — coroutine values inside the
listcomp are dropped to PyVal.none, but their effects flow through).
"""

import asyncio


async def fetch_one(url):
    return await async_fetch(url)


async def main(urls):
    coros = [fetch_one(u) for u in urls]
    results = await asyncio.gather(*coros)
    return results


assert main is not None

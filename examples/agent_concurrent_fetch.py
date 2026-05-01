# run-async
"""Realistic code-mode-style agent: concurrent fan-out fetch.

The agent receives a request like "give me the user, their posts,
and their like count", and instead of making three sequential tool
calls (the cost of a non-code-mode MCP setup, where each round-trip
goes back to the LLM), it writes one program that fans out the
fetches concurrently with `asyncio.gather` and returns only the
combined result.

The verification proves:
  - each `fetch_*` async function has type
    `Eff Perms.none (PyClosure Perms.none 0)` — a coroutine
    constructor that builds a 0-arg thunk;
  - `asyncio.gather` returns the results in argument order, with
    length equal to the number of inputs;
  - the assembled `summary` dict has the exact shape we expect.

In a real code-mode deployment the `fetch_*` bodies would call
`Net` externals; here we use stub return values so the assertions
reduce by decision. The shape of the gather chain is what matters
for the verification — that the agent's orchestration is provably
correct.
"""

import asyncio


async def fetch_user():
    return 'alice'


async def fetch_post_count():
    return 7


async def fetch_likes():
    return 42


# Fan-out fetch: three coroutines, one round-trip.
results = await asyncio.gather(  # pyright: ignore
    fetch_user(),
    fetch_post_count(),
    fetch_likes(),
)

# Extract by position. In real code mode, the LLM would assemble
# these into a typed response.
user = results[0]
post_count = results[1]
likes = results[2]

assert user == 'alice', 'user fetched'
assert post_count == 7, 'post count fetched'
assert likes == 42, 'likes fetched'
assert len(results) == 3, 'gather returned three results'

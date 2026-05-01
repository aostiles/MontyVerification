"""Realistic code-mode-style agent: ETL filter pipeline.

The pattern: an LLM is asked "give me the top scoring records
above 70, doubled". In a non-code-mode setup, that would require
several round trips: list records, filter, transform, return. With
code mode the LLM writes the whole pipeline once and the runtime
returns just the final result.

Pure throughout — no externals — so the WHOLE module reduces by
decision and we can witness the exact final values. This is the
"verifiable analytics" use case for the verification surface: the
caller cites a Lean theorem instead of trusting the LLM's plan
output."""


def is_passing(score: int) -> Pure[bool]:
    return score >= 70


def is_top(score: int) -> Pure[bool]:
    return score >= 90


def double(score: int) -> Pure[int]:
    return score * 2


# The agent's pipeline. Each stage uses a list comprehension over
# the previous one, making the data flow obvious to both the LLM
# and the verifier.
scores = [85, 92, 78, 95, 60, 88, 73, 99, 45, 81]

# Stage 1: filter to passing scores
passing = [s for s in scores if s >= 70]

# Stage 2: filter to top scores
top = [s for s in scores if s >= 90]

# Stage 3: doubled top scores
top_doubled = [s * 2 for s in scores if s >= 90]

# Stage 4: count buckets
passing_count = len(passing)
top_count = len(top)

assert passing_count == 8, 'eight passing scores'
assert top_count == 3, 'three top scores'
assert passing == [85, 92, 78, 95, 88, 73, 99, 81], 'passing values in order'
assert top == [92, 95, 99], 'top values in order'
assert top_doubled == [184, 190, 198], 'doubled top values'

# Spot-check the helpers directly
assert is_passing(85) == True, 'is_passing 85'
assert is_passing(60) == False, 'not passing 60'
assert is_top(95) == True, 'is_top 95'
assert is_top(85) == False, 'not top 85'
assert double(50) == 100, 'double 50'

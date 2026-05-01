# call-external
"""Demonstrates four symbolic-execution properties on one agent body.

Phase C of the symbolic-execution layer adds:
  - calledExactlyOnce target — count = 1 on every path
  - mutuallyExclusive a b — no path calls both
  - calledAfter a b — every call to a is followed by b on every path
  - eventuallyCalls target — every return path calls target

The agent below exercises all four against a single ETL-shaped
workflow: open the source, read it, optionally validate, write to
the destination, close the source, log the result.
"""


def run_etl(src, dst, validate):
    handle = open_source(src)
    data = read_data(handle)
    if validate:
        check_invariants(data)
    write_destination(dst, data)
    close_source(handle)
    log_completion(src, dst)
    return data

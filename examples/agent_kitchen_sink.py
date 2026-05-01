# call-external
"""Comprehensive demo: an agent that exercises every verification
capability the system has, on a single realistic shape.

The agent fetches a topic, summarizes it, optionally retries on
failure, generates a report, and notifies a recipient. It is split
across helper functions, has no `Pure[]` / `Effect[]` annotations,
and the matching `.lean` proves:

  1. Effect inference recovers the right `{ net := true }` type for
     each helper and the top-level entry point.
  2. The pure `clamp` helper reduces by `native_decide`.
  3. Ordering invariants on the tool-call sequence:
     - search → summarize on every path
     - summarize → generate_report on every path
     - generate_report → send_notification on every path
  4. The interprocedural variant works across the helper boundary
     (the entry point only sees the helper names; the inter-
     procedural walker inlines them to see the externals).
  5. `eventuallyCalls` proves every reachable return path notifies
     the recipient.
  6. `mutuallyExclusive` proves the success and failure paths
     don't both fire (a sanity check on the if/else structure).
"""


def clamp(value, lo, hi):
    if value < lo:
        return lo
    if value > hi:
        return hi
    return value


def fetch_step(topic):
    raw = search_web(topic)
    return raw


def summarize_step(raw, max_chars):
    bounded = clamp(max_chars, 100, 5000)
    summary = summarize(raw)
    return summary


def report_step(summary):
    return generate_report(summary)


def notify_step(recipient, report):
    send_notification(recipient, report)
    return report


def run_agent(topic, recipient, max_chars):
    raw = fetch_step(topic)
    summary = summarize_step(raw, max_chars)
    report = report_step(summary)
    notify_step(recipient, report)
    return report


# Pure helper assertions reduce by computation.
assert clamp(50, 100, 5000) == 100, 'clamp lower bound'
assert clamp(10000, 100, 5000) == 5000, 'clamp upper bound'
assert clamp(2000, 100, 5000) == 2000, 'clamp pass-through'

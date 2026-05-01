# call-external
"""Stress test 1: multi-stage retry with exponential backoff.

This is what an LLM might write for "fetch a URL with up to N retries,
backing off between attempts." The shape exercises:
  - bounded for-loop
  - try/except inside the loop
  - early return on success
  - state mutation across iterations (last_error)
"""


def fetch_with_retry(url, max_attempts):
    last_error = None
    for attempt in range(max_attempts):
        try:
            result = fetch_url(url)
            return result
        except Exception as exc:
            last_error = exc
            wait_seconds(2 ** attempt)
    raise last_error


assert fetch_with_retry is not None

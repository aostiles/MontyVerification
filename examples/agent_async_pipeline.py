# call-external
# external: fetch_document net
# external: extract_entities net
# external: store_results fs
# external: send_notification net
# external: log_completion fs
"""Interprocedural ordering across a multi-helper pipeline.

A document-processing agent: fetch, extract entities, store,
notify, and log. Each step is a separate helper function. The
matching `.lean` verifies:

  - Effect types are inferred correctly (no annotations needed).
  - Ordering invariants hold across helper function boundaries
    using interprocedural symbolic execution.
  - Every path logs completion (resource cleanup guarantee).
  - Each external is called exactly once (no double-fetch bugs).
"""


def fetch(doc_id):
    return fetch_document(doc_id)


def process(doc):
    entities = extract_entities(doc)
    store_results(entities)
    return entities


def notify_and_log(user, result):
    send_notification(user, result)
    log_completion(result)


def run_pipeline(doc_id, user):
    doc = fetch(doc_id)
    result = process(doc)
    notify_and_log(user, result)
    return result

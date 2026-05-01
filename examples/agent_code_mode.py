# call-external
# external: get_weather net
# external: store_result fs
# external: send_report net
"""Code-mode integration demo: the patterns LLM code-mode generates.

Exercises the two shapes code-mode produces most often:
  1. For-loop accumulating tool results into a dict via subscript
     assignment (`results[city] = w`).
  2. Sequential tool calls with ordering invariants.

The matching `.lean` verifies effect inference, ordering invariants,
and interprocedural analysis across helpers.
"""


def fetch_all(cities):
    results = {}
    for city in cities:
        w = get_weather(city)
        results[city] = w
    return results


def process_and_report(cities, recipient):
    data = fetch_all(cities)
    store_result(data)
    send_report(recipient, data)
    return data

# call-external
"""Stress test 4: dict-of-handlers dispatch.

A common LLM-pattern: build a dispatch table indexed by op name.
Should hit Perms.top widening because the call goes through a
PyVal-erased dict lookup.
"""


def handle_create(payload):
    return create_resource(payload)


def handle_delete(payload):
    return delete_resource(payload)


def handle_update(payload):
    return update_resource(payload)


def dispatch(op, payload):
    handlers = {
        'create': handle_create,
        'delete': handle_delete,
        'update': handle_update,
    }
    return handlers[op](payload)


assert dispatch is not None

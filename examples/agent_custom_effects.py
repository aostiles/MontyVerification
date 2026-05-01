# external: query_db db
# external: write_audit audit
# external: send_email net
"""Custom effects demo: declare effect kinds beyond net/fs/env/time.

The four hardcoded effects (net/fs/env/time) cover the OS-level
boundaries but real production tool APIs have other meaningful
effect categories: database access, audit logging, GPU usage,
PII handling, etc. The custom-effects mechanism lets a deployer
declare these as first-class effect kinds.

`db` and `audit` are custom effect names — they're not in the
hardcoded `Perms` struct's bool fields. The codegen emits them in
the `custom : List String` field of `Perms`. The verification
treats them with the same subset semantics as the standard
effects.
"""


def lookup_user(user_id):
    return query_db(user_id)


def record_action(user_id, action):
    write_audit(user_id, action)
    return action


def notify_and_audit(user_id, recipient):
    user = lookup_user(user_id)
    send_email(recipient, user)
    record_action(user_id, "notified")
    return user

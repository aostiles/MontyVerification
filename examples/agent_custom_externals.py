# external: fetch_invoice net
# external: charge_card net
# external: write_audit_log fs
# external: read_secret env
"""Configurable externals demo: declare your own tool API in source.

This file uses externals (`fetch_invoice`, `charge_card`,
`write_audit_log`, `read_secret`) that are NOT in MontyVerification's
hardcoded `externalPerms` table. Without the source-directive
mechanism, the codegen would treat them as unknown externals at
`Perms.top`, forcing every caller to be widened.

The `# external: <name> <effects>` directives at the top of this
file tell the codegen to treat each external as having the
declared effect set. Now `process_invoice` is inferred as
`{ net := true, fs := true, env := true }` — the precise union
of its tool calls — and the matching `.lean` proves it via `rfl`.

The format of a directive line is:

    # external: <python_name> <effect1>[,<effect2>...]

Recognised effect tokens: `net`, `fs`, `env`, `time`, plus `pure`
(for `Perms.none`) and `top` (for `Perms.top`). Multiple effects
are comma-separated.
"""


def process_invoice(invoice_id):
    secret = read_secret('STRIPE_KEY')
    invoice = fetch_invoice(invoice_id)
    charge_card(invoice, secret)
    write_audit_log(invoice_id)
    return invoice

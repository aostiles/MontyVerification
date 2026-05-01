"""Negative example: a REPL session that tries to call generate_report
in turn 2 without having called summarize in turn 1. The verification
must reject the chain.

The Python source is just placeholder; the protocol violation is
expressed in the paired `.lean` file."""


def trim(text: str, limit: int) -> Pure[str]:
    return text[:limit]


assert trim('hi', 100) == 'hi', 'placeholder'

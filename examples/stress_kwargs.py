# call-external
"""Stress test 10: keyword arguments and defaults.

Functions called with named kwargs, including some with defaults.
"""


def fetch(url, timeout=30, retries=3):
    return do_fetch(url, timeout, retries)


def main():
    a = fetch('http://a')
    b = fetch('http://b', timeout=60)
    c = fetch('http://c', timeout=10, retries=5)
    d = fetch(url='http://d', retries=1)
    return [a, b, c, d]


assert main is not None

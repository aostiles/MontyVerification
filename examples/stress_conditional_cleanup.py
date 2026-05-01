# call-external
"""Stress test 3: conditional cleanup (try/finally).

The "always close the resource even on error" pattern. Exercises:
  - try/finally
  - early return inside try
  - cleanup must run on every exit path
"""


def read_with_cleanup(path):
    handle = open_file(path)
    try:
        contents = read_handle(handle)
        if len(contents) == 0:
            return ''
        return contents
    finally:
        close_handle(handle)


assert read_with_cleanup is not None

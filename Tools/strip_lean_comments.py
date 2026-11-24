# SPDX-License-Identifier: Apache-2.0
"""Print a Lean file from stdin with its comments removed (block comments, nested, and line
comments), so two versions can be compared for code changes only."""

import sys


def strip(text: str) -> str:
    out = []
    i = 0
    depth = 0
    n = len(text)
    in_string = False
    while i < n:
        c = text[i]
        if depth == 0 and not in_string and text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        if not in_string and text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            elif text.startswith("/-", i):
                depth += 1
                i += 2
            else:
                i += 1
            continue
        if c == '"' and (i == 0 or text[i - 1] != "\\"):
            in_string = not in_string
        out.append(c)
        i += 1
    lines = [line.rstrip() for line in "".join(out).splitlines()]
    return "\n".join(line for line in lines if line.strip()) + "\n"


if __name__ == "__main__":
    sys.stdout.write(strip(sys.stdin.read()))

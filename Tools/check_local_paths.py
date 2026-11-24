# SPDX-License-Identifier: Apache-2.0
"""Fail when a tracked file names a machine-local absolute path.

Repository files must not depend on, or reveal, the layout of one machine: a user's home
directory, a scratch mount or an assistant's temporary directory. External inputs come from
command-line arguments or environment variables instead.

    python3 Tools/check_local_paths.py            # every tracked file
    python3 Tools/check_local_paths.py FILE ...   # the given files
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ROOTS = "home|raid|Users|root|scratch"
PATTERN = re.compile(r"(?<![\w.])/(?:" + ROOTS + r")/|/tmp" + r"/claude")


def tracked() -> list[str]:
    out = subprocess.run(
        ["git", "ls-files", "-z"], cwd=ROOT, check=True, capture_output=True
    ).stdout
    return [p for p in out.decode().split("\0") if p]


def offending(paths: list[str]) -> list[str]:
    found = []
    for rel in paths:
        path = ROOT / rel
        if not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for n, line in enumerate(text.splitlines(), 1):
            if PATTERN.search(line):
                found.append(f"{rel}:{n}: {line.strip()[:120]}")
    return found


def main(argv: list[str]) -> int:
    found = offending(argv or tracked())
    for line in found:
        print(line)
    if found:
        print(f"{len(found)} machine-local absolute path(s)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

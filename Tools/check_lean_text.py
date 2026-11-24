# SPDX-License-Identifier: Apache-2.0
"""Text checks on Lean sources that need no compilation.

* trailing whitespace; the file ends with exactly one newline
* forbidden words in code: `sorry`, `admit`, `native_decide`, and top-level `axiom`
  declarations (comments, doc strings and string literals do not count)
* optional line width (`--max-width N`, off by default; reported as errors when given). It
  agrees with Mathlib's `longLine` linter, which `lakefile.lean` turns on: a line that contains
  `http` is exempt, and so is a file with the line `set_option linter.style.longLine false`
  (only the generated `Ptx.lean` of a kernel whose PTX names are longer than a line has it)

Usage: python3 Tools/check_lean_text.py [--max-width N] [FILE ...]
With no files, every `.lean` file under the repository (except `.lake`) is checked.
"""

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_quotes import ROOT, split  # noqa: E402

LITERAL = re.compile(r"'\\?\"'|\"(?:[^\"\\]|\\.)*\"", re.S)
NO_LONG_LINE = "set_option linter.style.longLine false"
WORDS = re.compile(r"\b(sorry|admit|native_decide)\b")
AXIOM = re.compile(r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*axiom\b", re.M)


def blank_strings(text):
    return LITERAL.sub(
        lambda m: (
            m.group(0) if m.group(0).startswith("'") else '"' + "\n" * m.group(0).count("\n") + '"'
        ),
        text,
    )


def executable(src):
    """Source with comments and string contents removed, keeping line numbers."""
    lines = []
    for kind, text in split(src):
        if kind == "comment":
            lines.append("\n" * text.count("\n"))
        else:
            lines.append(blank_strings(text))
    return "".join(lines)


def check(path, src, max_width=0):
    """Return a list of (line, message)."""
    problems = []
    lines = src.split("\n")
    wide = max_width and NO_LONG_LINE not in lines
    for n, line in enumerate(lines, 1):
        if line != line.rstrip():
            problems.append((n, "trailing whitespace"))
        if wide and len(line) > max_width and "http" not in line:
            problems.append((n, f"line is {len(line)} characters (limit {max_width})"))
    if src and (not src.endswith("\n") or src.endswith("\n\n")):
        problems.append((len(lines), "file must end with exactly one newline"))
    body = executable(src)
    for n, line in enumerate(body.split("\n"), 1):
        for m in WORDS.finditer(line):
            problems.append((n, f"forbidden `{m.group(1)}` in code"))
    for m in AXIOM.finditer(body):
        problems.append((body.count("\n", 0, m.start()) + 1, "`axiom` declaration"))
    return problems


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--max-width", type=int, default=0, help="0 disables the width check")
    cli.add_argument("files", nargs="*", type=Path)
    args = cli.parse_args()
    files = args.files or sorted(
        f for f in ROOT.rglob("*.lean") if ".lake" not in f.relative_to(ROOT).parts
    )
    total = 0
    for path in files:
        for n, message in check(path, path.read_text(), args.max_width):
            print(f"{path}:{n}: {message}")
            total += 1
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())

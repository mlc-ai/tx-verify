# SPDX-License-Identifier: Apache-2.0
"""Check that double-quoted passages in model comments occur verbatim in the PTX ISA text.

A contract block that quotes the specification must quote it exactly (whitespace is
normalized; `[...]`, `…` and `...` separate fragments, each of which must occur). The
specification text is not part of this repository: give its path with `--spec` or the
`TXVERIFY_PTX_SPEC` environment variable. Without a path the check is skipped (exit 0).

The default files are Core, with the assumption constructors in Core/Assumption, Core/README.md,
and every kernel's assumption files, `Assumptions.lean` and the files under its `Assumptions/`; in
a kernel's assumption files the string literals (the assumptions' statements and template texts)
are checked as well as the comments. In a Markdown file the whole text is checked, with the
table separator `|` escaped by a backslash read as `|`.

Usage: python3 Tools/check_quotes.py [--spec ptx.txt] [PATH ...]
"""

import argparse
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ELLIPSIS = re.compile(r"\[\.\.\.\]|\[…\]|…|\.\.\.")


def split(src):
    """Return [(kind, text)] with kind in {"code", "comment"}; string literals are code."""
    out, i, n, start = [], 0, len(src), 0
    while i < n:
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            i = j + 1
        elif src.startswith(("'\"'", "'\\\"'"), i):
            i += 3 if src[i + 1] == '"' else 4
        elif src.startswith("--", i) or src.startswith("/-", i):
            if src.startswith("--", i):
                j = src.find("\n", i)
                j = n if j < 0 else j
            else:
                depth, j = 0, i
                while j < n:
                    if src.startswith("/-", j):
                        depth, j = depth + 1, j + 2
                    elif src.startswith("-/", j):
                        depth, j = depth - 1, j + 2
                        if depth == 0:
                            break
                    else:
                        j += 1
            out.append(("code", src[start:i]))
            out.append(("comment", src[i:j]))
            i = start = j
        else:
            i += 1
    out.append(("code", src[start:]))
    return out


def comments(src):
    return [t for k, t in split(src) if k == "comment"]


def strings(src):
    """String literals of the code, unescaped."""
    out = []
    for m in re.finditer(r'"((?:[^"\\]|\\.)*)"', code(src), re.S):
        out.append(re.sub(r"\\\n\s*", "", m.group(1)).replace('\\"', '"'))
    return out


def code(src):
    return "".join(t for k, t in split(src) if k == "code")


def norm(s):
    return " ".join(s.split())


def check(spec_text, files):
    """Return (verbatim count, [(file, quote)]) of unmatched quotes."""
    spec = norm(spec_text)
    ok, missing = 0, []
    for path in files:
        src = path.read_text()
        kernel_assumptions = path.name == "Assumptions.lean" or path.parent.name == "Assumptions"
        if path.suffix == ".md":
            texts = [src.replace("\\|", "|")]
        else:
            texts = comments(src) + (strings(src) if kernel_assumptions else [])
        for comment in texts:
            for m in re.finditer(r'"([^"]+)"', comment):
                quote = norm(m.group(1))
                if len(quote) < 4 or " " not in quote:
                    continue
                fragments = [x.strip() for x in ELLIPSIS.split(quote) if x.strip()]
                if all(x in spec for x in fragments):
                    ok += 1
                else:
                    missing.append((path, quote))
    return ok, missing


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--spec", type=Path, default=os.environ.get("TXVERIFY_PTX_SPEC"))
    cli.add_argument("paths", nargs="*")
    args = cli.parse_args()
    if not args.spec:
        print("skipped: no spec text")
        return 0
    if not Path(args.spec).is_file():
        print(f"error: spec text not found: {args.spec}", file=sys.stderr)
        return 2
    if args.paths:
        roots = [ROOT / p for p in args.paths]
    else:
        roots = [ROOT / "Core", ROOT / "Core/README.md"]
        roots += sorted((ROOT / "Kernels").glob("*/Assumptions.lean"))
        roots += sorted((ROOT / "Kernels").glob("*/Assumptions"))
    files = sorted({f for r in roots for f in ([r] if r.is_file() else r.rglob("*.lean"))})
    ok, missing = check(Path(args.spec).read_text(), files)
    print(f"quotes verbatim: {ok}; not verbatim: {len(missing)}")
    for path, quote in missing:
        print(f"MISS {path.relative_to(ROOT)} | {quote}")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())

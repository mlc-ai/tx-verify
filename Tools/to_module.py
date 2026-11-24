# SPDX-License-Identifier: Apache-2.0
"""Convert Lean source files to the module system.

Each file gets a ``module`` header, its imports become ``public import`` (``public meta
import`` for the Lean and Qq metaprogramming libraries, which tactic files run at
elaboration time), and its declarations are placed in an ``@[expose] public section`` so
that definitions keep their bodies for evaluation by ``decide`` and ``rfl`` while proofs
stay private to the module. Files already in module form are left unchanged.

    python Tools/to_module.py Core Lemmas ...   # directories or files
"""

import re
import sys
from pathlib import Path

META = ("Lean", "Qq", "Batteries.Lean")
IMPORT = re.compile(r"^import\s+(\S+)\s*$")


def convert(text: str) -> str | None:
    lines = text.split("\n")
    if any(line.strip() == "module" for line in lines[:20]):
        return None
    out, i = [], 0
    while i < len(lines) and (lines[i].startswith("--") or not lines[i].strip()):
        if lines[i].strip():
            out.append(lines[i])
        i += 1
    out.append("module")
    out.append("")
    while i < len(lines) and not lines[i].strip():
        i += 1
    imports_done = False
    while i < len(lines):
        line = lines[i]
        m = IMPORT.match(line)
        if m and not imports_done:
            name = m.group(1)
            meta = name == "Lean" or any(name.startswith(p + ".") or name == p for p in META)
            out.append(("public meta import " if meta else "public import ") + name)
            i += 1
            continue
        if not imports_done and line.strip() == "":
            out.append(line)
            i += 1
            continue
        if not imports_done:
            imports_done = True
            if out[-1].strip():
                out.append("")
            out.append("@[expose] public section")
            out.append("")
        out.append(line)
        i += 1
    if not imports_done:
        out.append("@[expose] public section")
        out.append("")
    return "\n".join(out)


def main(paths):
    changed = 0
    for arg in paths:
        p = Path(arg)
        files = sorted(p.rglob("*.lean")) if p.is_dir() else [p]
        for f in files:
            new = convert(f.read_text())
            if new is not None:
                f.write_text(new)
                changed += 1
    print(f"converted {changed} files")


if __name__ == "__main__":
    main(sys.argv[1:])

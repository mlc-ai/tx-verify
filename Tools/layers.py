# SPDX-License-Identifier: Apache-2.0
"""The layering of tml-fa4's Proof, as counters that fall to zero.

    Tools/layers.py [--list COUNTER]

A role's directories are its own; the layers above read its `Export/` modules only, and a role does
not read another role (but every scheduling role runs the scheduler, which is `Epilogue/`). The layers above do not open a role: no unfolding of the lane invariant, no
`import all`, no role reference invariant by name, no case split on the role of a state.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TREE = ROOT / "Kernels/TmlFa4Fwd/Proof"
PREFIX = "Kernels.TmlFa4Fwd.Proof."
ROLE = {
    "Epilogue": "epilogue",
    "Mma": "mma",
    "Loader": "loader",
    "LdWarp": "loader",
    "Softmax": "softmax",
    "SmWarp": "softmax",
    "Correction": "correction",
    "CorrWarp": "correction",
    "Startup": "startup",
}
UPPER = ("Protocol", "Top", "Progress", "Bound")
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(all\s+)?(\S+)", re.M)
REF = re.compile(
    r"\b(?:JR_eq|RefAll|Ref(?!Present\b)[A-Z]\w*|refE|(?:Mma|LdWarp|SmWarp|CorrWarp|Epilogue)\.Ref)\b"
)
SPLIT = re.compile(r"\b(?:cases|rcases) (?:i|σ1) with\b")
COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)


def counters(tree=TREE):
    """Counter name -> list of `file: item`."""
    out = {
        "upper imports of role internals": [],
        "imports between roles": [],
        "upper import all": [],
        "upper names of role invariants": [],
        "upper case splits on the role": [],
    }
    for path in sorted(tree.rglob("*.lean")):
        rel = path.relative_to(tree)
        top, text = rel.parts[0], path.read_text()
        code = COMMENT.sub("", text)
        for m in IMPORT.finditer(code):
            all_, name = m[1], m[2]
            if not name.startswith(PREFIX):
                continue
            parts = name[len(PREFIX) :].split(".")
            if top in UPPER:
                if parts[0] in ROLE and parts[1:2] != ["Export"]:
                    out["upper imports of role internals"].append(f"{rel}: {name}")
                if all_:
                    out["upper import all"].append(f"{rel}: {name}")
            elif top in ROLE and parts[0] in ROLE and "startup" not in (ROLE[top], ROLE[parts[0]]):
                if ROLE[parts[0]] not in (ROLE[top], "epilogue"):
                    out["imports between roles"].append(f"{rel}: {name}")
        if top in UPPER:
            code = IMPORT.sub("", code)
            out["upper names of role invariants"] += [f"{rel}: {m[0]}" for m in REF.finditer(code)]
            out["upper case splits on the role"] += [f"{rel}: {m[0]}" for m in SPLIT.finditer(code)]
    return out


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", metavar="COUNTER")
    args = ap.parse_args(argv)
    now = counters()
    if args.list:
        print("\n".join(now[args.list]))
    else:
        for name, items in now.items():
            print(f"{len(items):5}  {len({i.split(':')[0] for i in items}):4} files  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

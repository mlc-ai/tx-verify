# SPDX-License-Identifier: Apache-2.0
"""Report the size and duplication of a kernel proof directory.

Prints file/line totals, per-family totals (leading CamelCase words of the file
name), the most-repeated private declaration names, and counts of proof-limit
overrides. ``--json`` writes the same data for comparison between revisions.
"""

import argparse
import collections
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PRIVATE = re.compile(r"^private (?:theorem|lemma|def|abbrev) ([A-Za-z_][\w'.]*)", re.M)
WORDS = re.compile(r"[A-Z][a-z0-9]*")


def family(name: str, depth: int) -> str:
    return "".join(WORDS.findall(name)[:depth]) or name


def collect(folder: Path, depth: int):
    files = sorted(folder.rglob("*.lean"))
    fams = collections.Counter()
    fam_files = collections.Counter()
    privates = collections.Counter()
    total = 0
    limits = collections.Counter()
    for f in files:
        text = f.read_text()
        n = text.count("\n")
        total += n
        fam = family(f.stem, depth)
        fams[fam] += n
        fam_files[fam] += 1
        for m in PRIVATE.finditer(text):
            privates[m.group(1)] += 1
        limits["maxHeartbeats 0"] += text.count("maxHeartbeats 0")
        limits["maxRecDepth"] += text.count("maxRecDepth")
    return {
        "files": len(files),
        "lines": total,
        "families": {k: [fam_files[k], v] for k, v in fams.most_common()},
        "duplicate_private": {k: v for k, v in privates.most_common() if v > 1},
        "limits": dict(limits),
    }


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument(
        "folder", type=Path, nargs="?", default=ROOT / "Kernels" / "Fp16Gemm8192" / "Proof"
    )
    cli.add_argument("--depth", type=int, default=2, help="CamelCase words per family")
    cli.add_argument("--top", type=int, default=20)
    cli.add_argument("--json", type=Path)
    args = cli.parse_args()
    data = collect(args.folder, args.depth)
    print(f"{data['files']} files, {data['lines']} lines")
    print("limits:", data["limits"])
    print("families (files, lines):")
    for k, (nf, nl) in list(data["families"].items())[: args.top]:
        print(f"  {k:32} {nf:5} {nl:7}")
    dup = data["duplicate_private"]
    print(f"duplicated private names: {len(dup)} names, {sum(dup.values())} definitions")
    for k, v in list(dup.items())[: args.top]:
        print(f"  {k:32} {v}")
    if args.json:
        args.json.write_text(json.dumps(data, indent=1) + "\n")


if __name__ == "__main__":
    main()

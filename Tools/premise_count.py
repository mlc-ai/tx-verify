# SPDX-License-Identifier: Apache-2.0
"""Count the premises of tml-fa4's `correct2` beyond `Pre` (proof-architecture plan, rule P5).

`correct2` (`Proof/Top/Correct.lean`) proves the kernel correct for every launch that satisfies
`Pre`. A premise is any other hypothesis of it: a binder, a section variable other than the
launch's, an antecedent or a change of the conclusion, or a declaration of its file that could
stand for one (an axiom, a local definition). The count is zero and stays zero.

    python3 Tools/premise_count.py                 # the premises and their number
    python3 Tools/premise_count.py --total         # the number only
    python3 Tools/premise_count.py --roadmap FILE  # fail unless FILE's first "N open premises" is N

Without `--roadmap`, the environment variable `TXVERIFY_TMLFA4_ROADMAP` names the roadmap for
the pytest (`tests/test_premise_count.py`).
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOP = ROOT / "Kernels" / "TmlFa4Fwd" / "Proof" / "Top"
CORRECT = TOP / "Correct.lean"

NAME = "correct2"
NAMESPACE = "PTX.Kernels.TmlFa4Fwd.Proof.Top"
VARIABLES = ["{p : Params}", "{l : Launch}", "{m : Mem0}"]
HYPOTHESIS = "(hp : Pre p l m)"
CONCLUSION = "Correct kernel Assumptions.all l m (Post p m)"

DOC = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT = re.compile(r"--[^\n]*")
IMPORT = re.compile(r"^(?:public\s+)?import\s+(\S+)$")
COMMAND = re.compile(r"^(?=\S)", re.MULTILINE)
ROADMAP_COUNT = re.compile(r"(\d+) open premises")
OPENING, CLOSING = "([{\u2983", ")]}\u2984"


def strip_comments(text: str) -> str:
    """The source without block and line comments (doc comments included)."""
    return LINE_COMMENT.sub("", DOC.sub("", text))


def normal(text: str) -> str:
    """The text with every run of white space a single blank."""
    return " ".join(text.split())


def split_top(text: str, token: str) -> tuple[str, str] | None:
    """The text before and after the first `token` outside every bracket."""
    depth = 0
    for i, char in enumerate(text):
        if depth == 0 and text.startswith(token, i):
            return text[:i], text[i + len(token) :]
        depth += (char in OPENING) - (char in CLOSING)
    return None


def binders(text: str) -> list[str]:
    """The bracketed groups and the bare names of a binder list, in order."""
    out, depth, start = [], 0, None
    for i, char in enumerate(text):
        if start is None and not char.isspace():
            start = i
        depth += (char in OPENING) - (char in CLOSING)
        if start is not None and depth == 0 and (char in CLOSING or char.isspace()):
            out.append(normal(text[start : i + 1]))
            start = None
    if start is not None:
        out.append(normal(text[start:]))
    return out


def theorem_premises(command: str) -> list[str]:
    """What the theorem's statement assumes or changes beyond `Pre`."""
    head = split_top(command, ":=")
    statement = head[0] if head else command
    parts = split_top(statement, ":")
    if parts is None:
        return [f"no statement: {normal(command)}"]
    name, _, rest = parts[0].partition(NAME)
    out = [] if normal(name) == "theorem" else [f"modifier: {normal(name)}"]
    given = binders(rest)
    out += [f"hypothesis: {b}" for b in given if b != HYPOTHESIS]
    if HYPOTHESIS not in given:
        out.append(f"missing: {HYPOTHESIS}")
    if normal(parts[1]) != CONCLUSION:
        out.append(f"conclusion: {normal(parts[1])}")
    return out


def premises(text: str) -> list[str]:
    """Every premise of `correct2` in the source of its file."""
    out: list[str] = []
    found = 0
    for command in COMMAND.split(strip_comments(text)):
        command = command.strip()
        line = normal(command)
        if not line or line == "module" or IMPORT.match(line):
            continue
        if line in ("@[expose] public section", "section", "public section", "end", "open PTX"):
            continue
        if line in (f"namespace {NAMESPACE}", f"end {NAMESPACE}"):
            continue
        if line.startswith("variable "):
            given = binders(command[len("variable") :])
            out += [f"variable: {b}" for b in given if b not in VARIABLES]
        elif re.search(rf"\btheorem {NAME}\b", line):
            found += 1
            out += theorem_premises(command)
        else:
            out.append(f"declaration: {line}")
    if found != 1:
        out.append(f"{found} theorems {NAME}")
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", strip_comments(text)):
        out.append("sorry, admit, axiom or native_decide")
    return out


def count(path: Path = CORRECT) -> list[str]:
    """The premises of the tree's `correct2`."""
    return premises(path.read_text())


def roadmap_count(text: str) -> int | None:
    """The first "N open premises" of a roadmap."""
    match = ROADMAP_COUNT.search(text)
    return int(match.group(1)) if match else None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--total", action="store_true", help="print the total only")
    parser.add_argument("--roadmap", type=Path, help="roadmap whose count must agree")
    args = parser.parse_args(argv)
    found = count()
    if not args.total:
        for premise in found:
            print(premise)
    print(len(found) if args.total else f"{len(found):3d}  total")
    if args.roadmap is not None:
        written = roadmap_count(args.roadmap.read_text())
        if written != len(found):
            print(
                f"{args.roadmap}: says {written} open premises, counted {len(found)}",
                file=sys.stderr,
            )
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

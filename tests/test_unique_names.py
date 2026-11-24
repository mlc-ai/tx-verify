# SPDX-License-Identifier: Apache-2.0
"""Public declaration names of tml-fa4's Proof are unique (two would clash in one import)."""

import collections
import re
from pathlib import Path

TREE = Path(__file__).resolve().parents[1] / "Kernels/TmlFa4Fwd/Proof"
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected|nonrec)\s+)*"
    r"(?:theorem|def|abbrev|structure|inductive|lemma)\s+([\w.'«»]+)"
)


def test_names_are_unique():
    where = collections.defaultdict(set)
    for path in TREE.rglob("*.lean"):
        ns = []
        for line in re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S).split("\n"):
            if m := re.match(r"namespace (\S+)", line):
                ns.append(m[1])
            elif (m := re.match(r"end (\S+)", line)) and ns and ns[-1] == m[1]:
                ns.pop()
            elif m := DECL.match(line):
                name = m[1].removeprefix("_root_.")
                where[name if name != m[1] else ".".join([*ns, name])].add(str(path))
    assert not {n: sorted(p) for n, p in where.items() if len(p) > 1}

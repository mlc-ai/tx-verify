# SPDX-License-Identifier: Apache-2.0
"""Public declaration names of each proof tree are unique (two would clash in one import)."""

import collections
import re

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected|nonrec)\s+)*"
    r"(?:theorem|def|abbrev|structure|inductive|lemma)\s+([\w.'«»]+)"
)


def clashes(paths):
    """`{name: files}` of the names declared in more than one file."""
    where = collections.defaultdict(set)
    for path in paths:
        ns = []
        for line in re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S).split("\n"):
            if m := re.match(r"namespace (\S+)", line):
                ns.append(m[1])
            elif (m := re.match(r"end (\S+)", line)) and ns and ns[-1] == m[1]:
                ns.pop()
            elif m := DECL.match(line):
                name = m[1].removeprefix("_root_.")
                where[name if name != m[1] else ".".join([*ns, name])].add(str(path))
    return {n: sorted(p) for n, p in where.items() if len(p) > 1}


def test_clashes_are_found(tmp_path):
    (tmp_path / "A.lean").write_text("namespace N\ntheorem t : True := trivial\nend N\n")
    (tmp_path / "B.lean").write_text("theorem N.t : True := trivial\nprivate theorem u : 1 = 1\n")
    (tmp_path / "C.lean").write_text("private theorem u : 1 = 1\n")
    assert set(clashes(sorted(tmp_path.glob("*.lean")))) == {"N.t"}


def test_names_are_unique(tree):
    assert not clashes(tree.files(generated=True))

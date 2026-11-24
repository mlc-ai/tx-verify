# SPDX-License-Identifier: Apache-2.0
"""Modification cost (Tools/modcost.py): the rebuild rule, and the pattern counters' ceilings."""

import importlib
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"

# The counters of `modcost.counters` on 349d93bc7. They may fall, not rise; a commit that lowers
# one lowers its number here.
MAY_NOT_RISE = {
    "hData hN hD hS call lines": 0,
    "cases i with": 11,
    "lane invariant unfolded": 47,
    "positional projections": 152,
    "all_goals simp_all": 8,
    "code lookups per list element": 1,
    "role table re-entered": 0,
    "copied proof lines": 5525,
}


@pytest.fixture
def mc(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("modcost")


def graph(mc, files):
    return mc.Graph({m: mc.parse_header(text.splitlines()) for m, text in files.items()})


def mod(*imports):
    return "\n".join(["module", "", *imports])


def test_header(mc):
    text = "module\n\npublic import A.B\nimport C\npublic meta import D\nimport all E\n"
    is_module, imports = mc.parse_header(text.splitlines())
    assert is_module
    assert imports == [
        ("A.B", True, False, False),
        ("C", False, False, False),
        ("D", True, True, False),
        ("E", False, False, True),
    ]


def test_public_chain_reaches_everything(mc):
    g = graph(mc, {"A": mod(), "B": mod("public import A"), "C": mod("public import B")})
    assert g.downstream(["A"]) == {"A", "B", "C"}


def test_private_import_shields_the_importers(mc):
    g = graph(
        mc,
        {
            "A": mod(),
            "B": mod("import A"),
            "C": mod("public import B"),
            "D": mod("public import C"),
        },
    )
    assert g.downstream(["A"]) == {"A", "B"}
    assert g.downstream_static(["A"]) == {"A", "B", "C", "D"}
    assert g.upstream(["D"]) == {"A", "B", "C", "D"}


def test_private_import_sees_the_public_closure(mc):
    g = graph(
        mc,
        {
            "A": mod(),
            "B": mod("public import A"),
            "C": mod("import B"),
            "D": mod("public import C"),
        },
    )
    assert g.downstream(["A"]) == {"A", "B", "C"}


def test_meta_all_and_plain_files_see_private_imports(mc):
    g = graph(
        mc,
        {
            "A": mod(),
            "B": mod("import A"),
            "M": mod("public meta import B"),
            "L": mod("import all B"),
            "P": "import B\n",
            "N": mod("public import B"),
        },
    )
    assert g.downstream(["A"]) == {"A", "B", "M", "L", "P"}


def test_cost(mc):
    files = {
        "Kernels.K.Proof.Base": mod(),
        "Kernels.K.Proof.Top.Hand.X": mod("public import Kernels.K.Proof.Base"),
        "Kernels.K.Proof.Top.Y": mod("public import Kernels.K.Proof.Top.Hand.X"),
        "Kernels.J.Z": mod("public import Kernels.K.Proof.Base"),
    }
    times = {"Kernels.K.Proof.Base": 1.0, "Kernels.K.Proof.Top.Hand.X": 2.0}
    times |= {"Kernels.K.Proof.Top.Y": 4.0}
    g = graph(mc, files)
    out = mc.cost(g, ["Kernels.K.Proof.Base"], times)
    assert {k: len(v) for k, v in out["groups"].items()} == {
        "K Proof": 1,
        "K Proof Top/Hand": 1,
        "K Proof Top/": 1,
        "other kernel J": 1,
    }
    assert (out["seconds"], out["critical"], out["untimed"]) == (7.0, 7.0, 1)
    out = mc.cost(g, ["Kernels.K.Proof.Base"], times, "Kernels.K.Proof.Top.Hand.X")
    assert len(out["modules"]) == 2


def test_hunks(mc):
    diff = (
        "diff --git a/x b/x\n@@ -1 +1 @@\n-a\n+b\n@@ -9 +9 @@\ndiff --git a/y b/y\n@@ -0,0 +1 @@\n"
    )
    assert mc.hunks(diff) == {"x": 2, "y": 1}


def test_counter_definitions(mc, tmp_path):
    (tmp_path / "Top").mkdir()
    (tmp_path / "Top/A.lean").write_text(
        "f hData hN hD hS (g hData hN hD hS)\n  cases i with\nunfold JR\nh.2.2.2.1 h.2.2.2.2.2.2\n"
    )
    (tmp_path / "B.lean").write_text("cases i with\n")
    assert list(mc.counters(tmp_path).values()) == [1, 1, 1, 3, 0, 0, 0, 0]


def test_counters_do_not_rise(mc):
    now = mc.counters(ROOT / "Kernels/TmlFa4Fwd/Proof")
    assert set(now) == set(MAY_NOT_RISE)
    risen = {k: (n, MAY_NOT_RISE[k]) for k, n in now.items() if n > MAY_NOT_RISE[k]}
    assert not risen, f"counter: (now, ceiling) {risen}"

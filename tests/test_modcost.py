# SPDX-License-Identifier: Apache-2.0
"""Modification cost (Tools/modcost.py): the rebuild rule, and the pattern counters' ceilings."""

import importlib
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"


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


def test_counter_definitions(mc, make_tree):
    block = "".join(
        f"  have h{i} : some_long_fact_number_{i} = rfl_value_{i} := by simp\n" for i in range(14)
    )
    tree = make_tree(
        {
            "Top/A.lean": "f hData hN hD hS (g hData hN hD hS)\n  cases i with\nh.2.2.2.1 h.2.2.2.2.2.2\n"
            + "set_option maxHeartbeats 400000 in\nset_option maxHeartbeats 100000 in\n",
            "B/C.lean": "cases i with\nset_option maxHeartbeats 0 in\n" + "x\n" * 501,
            "Gen/D.lean": "h.2.2.2\n" + "x\n" * 600,
            "Protocol/E.lean": block,
            "B/F.lean": block,
            "B/G.lean": block,
        },
        patterns=[
            ["hData hN hD hS call lines", [""], "hData hN hD hS", False],
            ["cases i with", ["Top"], "cases i with", False],
        ],
    )
    got = mc.counters(tree)
    assert {k: v for k, v in got.items() if not k.startswith("handwritten lines")} == {
        "positional projections": 3,
        "maxHeartbeats raises": 2,
        "files over 500 lines": 1,
        "generated files outside Gen": 0,
        "modules unreachable from the top": 5,
        "common imports of role internals": 0,
        "copied proof lines zone A": 14,
        "copied proof lines zone B": 28,
        "hData hN hD hS call lines": 1,
        "cases i with": 1,
    }
    assert got["handwritten lines"] == 5 + 503 + 3 * 14
    assert got["handwritten lines Top/."] == 5
    assert got["handwritten lines Protocol/."] == 14
    assert got["handwritten lines B"] == 503 + 2 * 14
    assert mc.counter_items(tree, "copied proof lines zone A")[:1] == ["Protocol/E.lean:1"]
    assert mc.counter_items(tree, "files over 500 lines") == ["B/C.lean: 503 lines"]


def test_line_and_placement_counters(mc, make_tree):
    """Lines count by first directory, and by the second one under `Protocol/` and `Top/`; a file
    whose header names a generator must sit under `Gen/`; `Common/` may import role `Export/`
    modules only; every handwritten module is imported by the top module."""
    tree = make_tree(
        {
            "Top/Correct.lean": "import Kernels.K.Proof2.Top.Safe.X\nimport Kernels.K.Proof2.Common.C\n",
            "Top/Safe/X.lean": "import Kernels.K.Proof2.A.Export.E\nx\n",
            "Protocol/Values/V.lean": "-- Generated by Gen/v.py; do not edit.\nx\nx\n",
            "Common/C.lean": "import Kernels.K.Proof2.A.M\nimport Kernels.K.Proof2.A.Export.E\n",
            "A/M.lean": "",
            "A/Export/E.lean": "import Kernels.K.Proof2.A.M\n",
            "Gen/G.lean": "-- Generated by Gen/g.py\n",
        }
    )
    got = mc.counters(tree)
    assert got["handwritten lines Top/."] == 2
    assert got["handwritten lines Top/Safe"] == 2
    assert got["handwritten lines Protocol/Values"] == 3
    assert got["handwritten lines A"] == 1
    assert got["generated files outside Gen"] == 1
    assert got["common imports of role internals"] == 1
    assert mc.counter_items(tree, "modules unreachable from the top") == ["Protocol/Values/V.lean"]


def test_counters_under_their_ceilings(mc, tree):
    assert not tree.ceiling_violations(mc.counters(tree))

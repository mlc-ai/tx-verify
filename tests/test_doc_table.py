# SPDX-License-Identifier: Apache-2.0
"""The per-instruction tables of docs/core (`Tools/isa/doc_table.py`).

* the coverage file records, for every decoded entry, disjoint cubes of equal status whose union is
  exactly the legal modifier combinations of the entry, and every rule it names is a contract ID;
* the tables in the chapters are the ones the generator renders from the coverage file;
* with `TXVERIFY_BUILD=1`, a fresh run of `Tests/Source/IsaCoverage.lean` gives the committed coverage.
"""

import itertools
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
ISA = ROOT / "Tools" / "isa"


@pytest.fixture(scope="module")
def tools():
    sys.path.insert(0, str(ISA))
    sys.path.insert(0, str(ROOT / "Tools"))
    import coredoc
    import doc_table
    import gen_lean

    return {
        "doc_table": doc_table,
        "coredoc": coredoc,
        "m": gen_lean.build_model(),
        "cov": doc_table.load(),
    }


def test_coverage_cubes_are_the_legal_combinations(tools):
    """Per entry, the status cubes are disjoint and cover the legal combinations exactly."""
    cov, m = tools["cov"], tools["m"]
    assert set(cov["entries"]) == {e["name"] for e in m.entries}
    for e in m.entries:
        rec = cov["entries"][e["name"]]
        points = set()
        for st in rec["statuses"]:
            cube_points = set()
            for cube in st["cubes"]:
                pts = set(itertools.product(*cube))
                assert not cube_points & pts, e["name"]
                cube_points |= pts
            assert len(cube_points) == st["count"], e["name"]
            assert not points & cube_points, f"{e['name']}: two statuses share a combination"
            points |= cube_points
        assert points == set(e["variants"]), e["name"]
        assert rec["head"]["combinations"] == len(e["variants"])


def test_every_rule_is_a_contract_id(tools):
    """A `core` status names a rule that exists as a contract block, and every rule of
    `Core/Isa/Rule.lean` is such a block."""
    repo = tools["coredoc"].Repo(ROOT)
    named = set(re.findall(r'=> "([A-Z0-9-]+)"', (ROOT / "Core/Isa/Rule.lean").read_text()))
    assert named
    for ident in named:
        assert ident in repo.comments, ident
    for name, rec in tools["cov"]["entries"].items():
        for st in rec["statuses"]:
            kind, _, rest = st["status"].partition(" ")
            assert kind in ("core", "decode-only", "rejected"), (name, st["status"])
            if kind == "core":
                assert rest in named, (name, rest)


def test_tables_are_fresh(tools):
    """The chapters contain exactly the tables rendered from the coverage file."""
    coredoc = tools["coredoc"]
    files, errors, _, _ = coredoc.render_all(ROOT)
    assert not errors
    text = files["docs/core/instructions.md"]
    assert (ROOT / "docs/core/instructions.md").read_text() == text
    for rec in tools["cov"]["entries"].values():
        assert f"`{tools['doc_table'].syntax(rec)}`" in text


def test_row_cells(tools):
    """The cells of a row: the slot values with semantics and those that decode only."""
    dt = tools["doc_table"]
    rec = {
        "head": {
            "family": "int",
            "mnemonic": "add",
            "effect": "local",
            "section": "9.7.1.1",
            "slots": [["sat", True], ["type", False]],
            "operands": "d, a, b",
            "combinations": 4,
        },
        "statuses": [
            {"status": "core THREAD-INT", "count": 2, "cubes": [[[""], ["s32", "u32"]]]},
            {"status": "decode-only", "count": 2, "cubes": [[["sat"], ["s32", "u32x2"]]]},
        ],
    }
    assert dt.syntax(rec) == "add{.sat}.type"
    cell = dt.modifier_cell(rec)
    assert "**With semantics:** sat: (omitted); type: `s32`, `u32`" in cell
    assert "**Decode only:** sat: `sat`; type: `u32x2`" in cell
    status = dt.status_cell(rec)
    assert "Core semantics (2 of 4)" in status
    assert "an `Assumption.localRule` may give it a meaning" in status
    rec["head"]["effect"] = "event"
    assert "execution is rejected" in dt.status_cell(rec)
    link = lambda ident: f"x.md#{ident}"  # noqa: E731
    assert dt.rule_cell(rec, link) == "[THREAD-INT](x.md#THREAD-INT)"


def test_cubes_cover_exactly(tools):
    dt = tools["doc_table"]
    points = {("a", "x"), ("a", "y"), ("b", "x"), ("c", "z")}
    cubes = dt.cubes_of(points, 2)
    covered = set()
    for c in cubes:
        covered |= set(itertools.product(*c))
    assert covered == points
    assert sum(len(list(itertools.product(*c))) for c in cubes) == len(points)


@pytest.mark.skipif(os.environ.get("TXVERIFY_BUILD") != "1", reason="set TXVERIFY_BUILD=1")
def test_coverage_is_fresh():
    """A fresh run of `Tests/Source/IsaCoverage.lean` over every legal combination gives the committed
    docs/core/isa-coverage.json."""
    result = subprocess.run(
        [sys.executable, str(ISA / "doc_table.py"), "--check"], capture_output=True, text=True
    )
    assert result.returncode == 0, result.stdout + result.stderr

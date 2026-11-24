# SPDX-License-Identifier: Apache-2.0
"""Tools/out_gen.py: straight-line runs as pieces with stated values, and their freshness."""

import copy
import importlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"
DECLS = sorted((ROOT / "Tests" / "Gen" / "Out").glob("*.json")) + sorted(
    ROOT.glob("Kernels/*/Gen/Out/*.json")
)
EXPO = ROOT / "Tests" / "Gen" / "Out" / "expo.json"


@pytest.fixture(scope="module")
def og():
    sys.path.insert(0, str(TOOLS))
    return importlib.import_module("out_gen")


@pytest.fixture
def decl():
    return json.loads(EXPO.read_text())


@pytest.mark.parametrize("path", DECLS, ids=lambda p: str(p.relative_to(ROOT)))
def test_generated_runs_are_fresh(path):
    r = subprocess.run(
        [sys.executable, str(TOOLS / "out_gen.py"), str(path), "--check"],
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stdout + r.stderr


def with_run(decl, **kw):
    d = copy.deepcopy(decl)
    d["runs"][0].update(kw)
    return d


def test_pieces_and_values(og, decl):
    text = og.render(with_run(decl, start=4399, end=4404, cut=2, outputs=[]))
    # three pieces of 2, 2 and 1 items, composed into one run of 5
    assert "theorem expo_piece2 " in text and "theorem expo_piece3 " not in text
    assert "L g 5 4399 (expo_facts0 V) 4404" in " ".join(text.split())
    # the product's value is the term the code computes from the start values
    assert "def expo_v4399 (V : Nat → Value) : Value :=\n  okVal (.bits 32 0) (mulE false" in text
    # the packed fma reads the defs of the moves before it
    assert "(fma2E (expo_v4401 V) (expo_v4402 V) (expo_v4400 V))" in text


def test_live_facts(og, decl):
    text = og.render(with_run(decl, start=4399, end=4401, cut=32, outputs=[]))
    facts0 = text.split("def expo_facts0")[1].split("]")[0]
    # the product's operands are live at the start; its result is not (written in the run)
    assert facts0.count("V 3685") == 1 and facts0.count("V 1230") == 1
    assert "3686" not in facts0


def test_event_stops(og, decl):
    with pytest.raises(og.GenError, match="not an unguarded local instruction"):
        og.render(with_run(decl, end=4827))


def test_undeclared_reading(og, decl):
    with pytest.raises(og.GenError, match="has no item"):
        og.render(with_run(decl, fn={}))


def test_missing_rule(og, decl):
    rules = dict(decl["runs"][0]["rules"])
    del rules["ex2"]
    with pytest.raises(og.GenError, match="no rule declared for the item kind ex2"):
        og.render(with_run(decl, rules=rules))


def test_max_items(og):
    decl = json.loads((ROOT / "Tests" / "Gen" / "Out" / "max.json").read_text())
    d = copy.deepcopy(decl)
    d["runs"][0].update(start=5662, end=5666, outputs=[])
    text = " ".join(og.render(d).split())
    # three- and two-source `max.f32` are `fn` items with the library's outcome `maxE`
    assert ".fn (maxOp 4558 [4546, 4556, 4557]) 4558 [4546, 4556, 4557] maxE" in text
    assert ".fn (maxOp 4559 [4549, 4552]) 4559 [4549, 4552] maxE" in text
    assert "rule_max3 5663 rfl" in text and "rule_max2 5664 rfl" in text


def test_options(og, decl):
    d = with_run(decl, start=4399, end=4401, cut=32, outputs=[])
    d["options"] = {"maxRecDepth": 100000}
    assert "noncomputable section\nset_option maxRecDepth 100000\n" in og.render(d)
    assert "set_option maxRecDepth" not in og.render(with_run(decl, start=4399, end=4401))

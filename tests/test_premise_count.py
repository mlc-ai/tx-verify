# SPDX-License-Identifier: Apache-2.0
"""tml-fa4's `correct2` has no hypothesis beyond `Pre` (Tools/premise_count.py)."""

import importlib
import os
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"


@pytest.fixture
def pc(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("premise_count")


def test_correct2_assumes_only_pre(pc):
    assert pc.count() == []


HYP = "correct2 (hp : Pre p l m)"
GOAL = "Correct kernel Assumptions.all l m (Post p m)"
VARS = "variable {p : Params} {l : Launch} {m : Mem0}"


@pytest.mark.parametrize(
    "old, new",
    [
        (HYP, HYP + " (hR : Rest p l m)"),
        (HYP, HYP + "\n    (hR :\n      Rest p l m)"),
        (HYP, HYP + " {hR : Rest p l m}"),
        (HYP, HYP + " [Rest p l m]"),
        (HYP, HYP + " \u2983hR : Rest p l m\u2984"),
        (HYP, HYP + " hR"),
        (HYP, "correct2 (hp : Pre p l m \u2227 Rest p l m)"),
        (HYP, "correct2 (hp hR : Pre p l m)"),
        (HYP, "correct2"),
        (GOAL, "Rest p l m \u2192 " + GOAL),
        (GOAL, "\u2200 _ : Rest p l m, " + GOAL),
        (GOAL, "Correct kernel Assumptions.all l m (fun _ => True)"),
        (GOAL, "Correct kernel Assumptions.more l m (Post p m)"),
        (VARS, VARS + " (hR : Rest p l m)"),
        (VARS, VARS + "\n\nvariable [Fact (Rest p l m)]"),
        (VARS, VARS + "\n\ninclude hR"),
        (VARS, VARS + "\n\naxiom rest : Rest p l m"),
        (VARS, VARS + "\n\ndef Pre (p : Params) : Prop := False"),
        (VARS, VARS + '\n\nlocal notation "Pre" => Rest'),
        (VARS, VARS + "\n\nopen Other"),
        ("theorem correct2", "private theorem correct2"),
        ("theorem correct2", "theorem correct3"),
        (":=\n", ":= by sorry\n"),
    ],
)
def test_a_gained_premise_is_found(pc, old, new):
    text = pc.CORRECT.read_text()
    assert pc.premises(text) == []
    assert old in text
    assert pc.premises(text.replace(old, new)) != []


def test_comments_are_not_premises(pc):
    text = pc.CORRECT.read_text()
    assert pc.premises(text + "\n-- axiom rest\n/- variable (h : Rest) -/\n") == []


def test_no_premise_bundle_in_the_top_level(pc):
    bundle = re.compile(
        r"^(?:structure|class|def|abbrev) (?:\S+\.Rest|\S*Premises?|ProgressRest|BaseS?)\b", re.M
    )
    for path in sorted(pc.TOP.rglob("*.lean")):
        assert bundle.findall(pc.strip_comments(path.read_text())) == [], path


@pytest.mark.parametrize(
    "file, name",
    [
        ("Safety.lean", "safe"),
        ("Result/Output.lean", "Res.output"),
        ("Result/Lse.lean", "Res.lse"),
    ],
)
def test_the_goals_assume_only_pre_and_the_execution(pc, file, name):
    """A goal theorem takes `Pre`, an execution, its consistency and its completeness."""
    text = pc.strip_comments((pc.TOP / file).read_text())
    match = re.search(rf"^theorem {re.escape(name)}\b", text, re.M)
    statement = pc.split_top(text[match.end() :], ":=")[0]
    given = pc.binders(pc.split_top(statement, " :")[0])
    allowed = {
        "(hp : Pre p l m)",
        "{X : Execution}",
        "(hX : Consistent l kernel Assumptions.all m X)",
        "(hC : Complete l X)",
    }
    assert set(given) <= allowed


def test_roadmap_number(pc):
    assert pc.roadmap_count("Current (today): 32 open premises (D 16)") == 32
    assert pc.roadmap_count("no number") is None


def roadmap() -> Path | None:
    env = os.environ.get("TXVERIFY_TMLFA4_ROADMAP")
    if env:
        return Path(env)
    sibling = ROOT.parent / "tmlfa4-roadmap.md"
    return sibling if sibling.exists() else None


def test_roadmap_agrees(pc):
    path = roadmap()
    if path is None:
        pytest.skip("no tml-fa4 roadmap (set TXVERIFY_TMLFA4_ROADMAP)")
    assert pc.roadmap_count(path.read_text()) == len(pc.count())

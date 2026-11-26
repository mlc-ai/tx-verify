# SPDX-License-Identifier: Apache-2.0
"""The top theorem of each tree assumes only `Pre` (closed) or `Pre` and the ledger's `Open`
(Tools/premise_count.py)."""

import os
import re
from pathlib import Path

import premise_count as pc
import pytest
import trees

ROOT = Path(__file__).resolve().parents[1]
CLOSED = [t for t in trees.load() if t.closed]
TMLFA4 = next((t for t in CLOSED if t.kernel == "TmlFa4Fwd"), None)


def test_the_ledger_holds(tree):
    """A closed tree: no premise. An open tree: the ledger names exactly the leaves of `Open`,
    a new one is a registered split of one the merge base had."""
    assert pc.ledger_problems(tree, tree.base_config()) == []


def test_tmlfa4_is_closed_and_correct2_assumes_only_pre():
    assert TMLFA4 is not None and TMLFA4.top["theorem"] == "correct2"
    assert pc.count(TMLFA4) == []


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
        (HYP, HYP + " ⦃hR : Rest p l m⦄"),
        (HYP, HYP + " hR"),
        (HYP, "correct2 (hp : Pre p l m ∧ Rest p l m)"),
        (HYP, "correct2 (hp hR : Pre p l m)"),
        (HYP, "correct2"),
        (GOAL, "Rest p l m → " + GOAL),
        (GOAL, "∀ _ : Rest p l m, " + GOAL),
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
def test_a_gained_premise_is_found(old, new):
    top = pc.Top(TMLFA4)
    text = top.correct.read_text()
    assert pc.premises(text, top) == []
    assert old in text
    assert pc.premises(text.replace(old, new), top) != []


def test_comments_are_not_premises():
    top = pc.Top(TMLFA4)
    text = top.correct.read_text()
    assert pc.premises(text + "\n-- axiom rest\n/- variable (h : Rest) -/\n", top) == []


@pytest.mark.parametrize("closed_tree", CLOSED, ids=[t.kernel for t in CLOSED])
def test_no_premise_bundle_in_the_top_level(closed_tree):
    bundle = re.compile(
        r"^(?:structure|class|def|abbrev) (?:\S+\.Rest|\S*Premises?|ProgressRest|BaseS?|Open)\b",
        re.M,
    )
    for path in sorted(pc.Top(closed_tree).correct.parent.rglob("*.lean")):
        assert bundle.findall(pc.strip_comments(path.read_text())) == [], path


@pytest.mark.parametrize(
    "file, name",
    [
        ("Safety.lean", "safe"),
        ("Result/Output.lean", "Res.output"),
        ("Result/Lse.lean", "Res.lse"),
    ],
)
def test_the_goals_assume_only_pre_and_the_execution(file, name):
    """A goal theorem takes `Pre`, an execution, its consistency and its completeness."""
    text = pc.strip_comments((TMLFA4.root / "Top" / file).read_text())
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


# An open tree, synthetic.

OPEN = """module
namespace PTX.Kernels.K.Proof2.Top

structure SafeRest (p : Params) : Prop where
  noRace : NoRace p
  /-- a doc comment
  over lines -/
  noOob :
    NoOob p

structure ProgOpen (p : Params) : Prop where
  done : Done p

structure Open (p : Params) : Prop extends ProgOpen p where
  safe : SafeRest p
  follow : Follow p

end PTX.Kernels.K.Proof2.Top
"""

CORRECT = """module
namespace PTX.Kernels.K.Proof2.Top
variable {p : Params}

theorem correct (hp : Pre p) (ho : Open p) : Correct p := sorry_free

end PTX.Kernels.K.Proof2.Top
"""


def ledger(*names, **splits):
    out = {n: {"owner": "LA", "split_of": None} for n in names}
    for n, parent in splits.items():
        out[n] = {"owner": "LA", "split_of": parent}
    return out


def test_open_leaves(make_tree):
    tree = make_tree({"Top/Open.lean": OPEN, "Top/Correct.lean": CORRECT})
    leaves = ["done", "safe.noRace", "safe.noOob", "follow"]
    assert pc.open_leaves(tree) == leaves
    assert pc.count(tree) == [f"open: {n}" for n in leaves]


def test_an_extra_binder_is_a_premise(make_tree):
    text = CORRECT.replace("(ho : Open p)", "(ho : Open p) (hR : Rest p)")
    tree = make_tree({"Top/Open.lean": OPEN, "Top/Correct.lean": text})
    assert pc.count(tree)[-1] == "hypothesis: (hR : Rest p)"


@pytest.mark.parametrize(
    "premises, base, problems",
    [
        (ledger("done", "safe.noRace", "safe.noOob", "follow"), None, 0),
        (ledger("done", "safe.noRace", "safe.noOob"), None, 1),  # follow missing from the ledger
        (ledger("done", "safe.noRace", "safe.noOob", "follow", "x"), None, 1),  # x not in Open
        # three names the base does not have and that are no splits
        (ledger("done", "safe.noRace", "safe.noOob", "follow"), ledger("done", *"abcd"), 3),
        # one new name that is no split
        (
            ledger("done", "safe.noRace", "safe.noOob", "follow"),
            ledger("done", "safe.noRace", "follow"),
            1,
        ),
        # a split whose parent is still open adds a premise
        (
            ledger("done", "safe.noRace", "follow", **{"safe.noOob": "follow"}),
            ledger("done", "safe.noRace", "follow"),
            1,
        ),
        # safe.noOob and follow are new, split from `safety` that the base had
        (
            ledger("done", "safe.noRace", **{"safe.noOob": "safety", "follow": "safety"}),
            ledger("done", "safe.noRace", "safety", "other"),
            0,
        ),
        (
            ledger("done", "safe.noRace", **{"safe.noOob": "safety", "follow": "safe.nothing"}),
            ledger("done", "safe.noRace", "safety", "other"),
            1,
        ),
    ],
)
def test_the_ledger(make_tree, premises, base, problems):
    tree = make_tree({"Top/Open.lean": OPEN, "Top/Correct.lean": CORRECT}, premises=premises)
    base_cfg = None if base is None else {"closed": False, "premises": base}
    assert len(pc.ledger_problems(tree, base_cfg)) == problems


NESTED = """module
namespace PTX.Kernels.K.Proof2.Top

structure Safe.NoUb.Rest (p : Params) : Prop where
  whole : Whole p

namespace Bound
structure Rest (p : Params) : Prop where
  bound : B p
end Bound

namespace Res.Output
structure Rest (p : Params) : Prop where
  values : V p
  frame : F p
end Res.Output

namespace Other
/-- A `Rest` that `Open` does not name: its fields do not count. -/
structure Rest (p : Params) : Prop where
  decoy : D p
end Other

end PTX.Kernels.K.Proof2.Top
"""

NESTED_OPEN = """module
namespace PTX.Kernels.K.Proof2.Top
open PTX

structure Open (p : Params) : Prop where
  follow : Follow p
  /-- doc -/
  noUb : Safe.NoUb.Rest p
  bound : Bound.Rest p
  output :
    Res.Output.Rest p
  lse : PTX.Kernels.K.Proof2.Top.Res.Lse.Rest p

end PTX.Kernels.K.Proof2.Top
"""

LSE = """module
namespace PTX.Kernels.K.Proof2.Top.Res.Lse
structure Rest (p : Params) : Prop where
  values : V p
  empty : E p
end PTX.Kernels.K.Proof2.Top.Res.Lse
"""


def test_same_named_rest_structures_in_different_namespaces(make_tree):
    """Each `Rest` is found by its qualified name, declared dotted or inside a namespace; a leaf
    is named by its path from `Open`."""
    files = {
        "Top/Open.lean": NESTED_OPEN,
        "Top/Classes.lean": NESTED,
        "Top/Result/Lse.lean": LSE,
        "Top/Correct.lean": CORRECT,
    }
    leaves = [
        "follow",
        "noUb.whole",
        "bound.bound",
        "output.values",
        "output.frame",
        "lse.values",
        "lse.empty",
    ]
    tree = make_tree(files, premises=ledger(*leaves))
    assert pc.open_leaves(tree) == leaves
    assert pc.ledger_problems(tree, None) == []
    # A new name is a registered split of a dotted leaf of the base.
    base = {"closed": False, "premises": ledger(*leaves[:-1], "lse.all")}
    split = {**ledger(*leaves[:-2]), **ledger(**{"lse.values": "lse.all", "lse.empty": "lse.all"})}
    tree = make_tree(files, premises=split)
    assert pc.ledger_problems(tree, base) == []
    small = {"closed": False, "premises": ledger(*leaves[:5])}
    assert len(pc.ledger_problems(tree, small)) == 2  # two new names whose parent the base lacks


def test_roadmap_number():
    assert pc.roadmap_count("Current (today): 32 open premises (D 16)") == 32
    assert pc.roadmap_count("no number") is None


def roadmap() -> Path | None:
    env = os.environ.get("TXVERIFY_TMLFA4_ROADMAP")
    if env:
        return Path(env)
    sibling = ROOT.parent / "tmlfa4-roadmap.md"
    return sibling if sibling.exists() else None


def test_roadmap_agrees():
    path = roadmap()
    if path is None:
        pytest.skip("no tml-fa4 roadmap (set TXVERIFY_TMLFA4_ROADMAP)")
    assert pc.roadmap_count(path.read_text()) == len(pc.count(TMLFA4))

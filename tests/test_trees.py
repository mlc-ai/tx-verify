# SPDX-License-Identifier: Apache-2.0
"""Tools/trees.py: the trees, their paths, and ceilings that only fall."""

import json
import subprocess

import pytest
import trees

KEYS = {
    "kernel",
    "root",
    "namespace",
    "roles",
    "common",
    "lower",
    "upper",
    "generated",
    "state_names",
    "top",
    "closed",
    "ceilings",
}


def test_every_tree_has_the_schema(tree):
    assert KEYS <= set(tree.cfg), KEYS - set(tree.cfg)
    assert tree.root.is_dir()
    assert (tree.root / tree.top["correct"]).exists()
    if not tree.closed:
        assert (tree.root / tree.top["open"]).exists()


def test_the_ceilings_do_not_rise_from_the_merge_base(tree):
    assert not tree.ceiling_violations({})


def test_tmlfa4_is_a_tree():
    assert "TmlFa4Fwd" in {t.kernel for t in trees.load()}


def test_names_and_paths(make_tree, tmp_path):
    tree = make_tree({"A/Ref.lean": "", "A/Export/E.lean": "", "Gen/S.lean": "", "Top/T.lean": ""})
    assert trees.module_name("Kernels/K/Proof2/A/Ref.lean") == "Kernels.K.Proof2.A.Ref"
    assert trees.module_name(tmp_path / "Kernels/K/X.lean", tmp_path) == "Kernels.K.X"
    assert trees.module_path("Kernels.K.X", tmp_path) == tmp_path / "Kernels/K/X.lean"
    root = tree.root
    assert tree.role_of(root / "A/Ref.lean") == ("role", "A")
    assert tree.role_of(root / "Top/T.lean") == ("upper", "Top")
    assert tree.role_of(root / "Iface/I.lean") == ("lower", "Iface")
    assert tree.role_of(root / "Common/Roles.lean") == ("common", "Common")
    assert tree.role_of(tmp_path / "Lemmas/X.lean") is None
    assert tree.is_role_internal(root / "A/Ref.lean")
    assert not tree.is_role_internal(root / "A/Export/E.lean")
    assert tree.is_generated(root / "Gen/S.lean")
    assert tree.is_generated(tmp_path / "Kernels/K/Gen/Step/S1.lean")
    assert [p.name for p in tree.files()] == ["E.lean", "Ref.lean", "T.lean"]
    assert tree.lanes_of("Kernels/K/Proof2/A/Ref.lean") == ["LA"]
    assert tree.lanes_of("Lemmas/Extra/X.lean") == ["LB", "L"]
    assert tree.lanes_of("Kernels/K/Proof2/Common/X.lean") == []
    assert tree.lanes_of("Kernels/K/Proof2/AB/X.lean") == []


def test_handwritten_lines(make_tree):
    tree = make_tree(
        {"A/X.lean": "a\nb\n", "A/Y.lean": "c\n", "Gen/S.lean": "x\n" * 9, "T.lean": "t"}
    )
    assert tree.handwritten_lines() == {".": 1, "A": 3}


def git(cwd, *args):
    subprocess.run(["git", "-C", str(cwd), *args], check=True, capture_output=True)


@pytest.fixture
def repo(tmp_path, make_tree, monkeypatch):
    """A git repository whose `main` has tree K with ceilings, and a branch `work` on it."""
    tree = make_tree(ceilings={"a": 5, "b": 3})
    git(tmp_path, "init", "-q", "-b", "main")
    git(tmp_path, "-c", "user.name=t", "-c", "user.email=t@t", "add", ".")
    git(tmp_path, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "base")
    git(tmp_path, "checkout", "-qb", "work")
    monkeypatch.setenv("TXVERIFY_BASE", "main")
    trees.merge_base.cache_clear()
    yield tree
    trees.merge_base.cache_clear()


def set_ceilings(tree, ceilings):
    cfg = json.loads(tree.config_path.read_text())
    cfg["ceilings"] = ceilings
    tree.config_path.write_text(json.dumps(cfg))
    return trees.Tree(tree.config_path, tree.repo)


def test_ceilings_against_the_merge_base(repo):
    assert set_ceilings(repo, {"a": 4, "b": 3}).ceiling_violations({"a": 4}) == []
    assert set_ceilings(repo, {"a": 6, "b": 3}).ceiling_violations({}) == [
        "K: ceiling a raised from 5 to 6"
    ]
    # A measured value above its ceiling; an absent ceiling is 0.
    assert len(set_ceilings(repo, {"a": 4}).ceiling_violations({"a": 5, "c": 1})) == 2


def test_lower_never_raises(repo):
    changed = repo.lower_ceilings({"a": 2, "b": 7, "c": 1})
    assert changed == {"a": (5, 2)}
    assert json.loads(repo.config_path.read_text())["ceilings"] == {"a": 2, "b": 3}


def test_load_by_name(make_tree, tmp_path):
    make_tree()
    assert [t.kernel for t in trees.load(["K"], tmp_path)] == ["K"]
    with pytest.raises(SystemExit):
        trees.load(["Nope"], tmp_path)


def test_report(make_tree):
    sites = (
        "def a : RoleDecl := ⟨[(0, 10), (20, 21)], [10]⟩\n"
        "def bHead : RoleDecl := ⟨[(10, 15)], [15]⟩\n"
        "def bIdle : RoleDecl := ⟨[(15, 20)], []⟩\n"
    )
    tree = make_tree(
        {
            "Common/Sites.lean": sites,
            "A/Ref.lean": "-- a\n" * 8,
            "A/Export/E.lean": "-- e\n" * 2,
            "B/X.lean": "-- b\n" * 5,
            "Top/Correct.lean": "-- t\n",
        },
        closed=True,
        instructions=21,
        ceilings={
            "handwritten lines A": 100,
            "handwritten lines Top/.": 50,
            "handwritten lines": 90,
        },
    )
    rows = {r["dir"]: r for r in trees.report(tree)}
    assert trees.role_instructions(tree) == {"A": 11, "B": 10}
    assert rows["A"]["lines"] == 10 and rows["A"]["per_instruction"] == round(10 / 11, 2)
    assert rows["A"]["export_share"] == 0.2
    assert rows["A"]["ceiling"] == 100 and rows["Top/."]["ceiling"] == 50
    assert rows["Top/."]["lines"] == 1 and "ceiling 1/50" in trees.report_line(rows["Top/."])
    assert rows["TOTAL"]["lines"] == 19 and rows["TOTAL"]["ceiling"] == 90
    assert rows["TOTAL"]["open_premises"] is None
    tree.cfg["role_instructions"] = {"A": 5}
    assert trees.role_instructions(tree) == {"A": 5}
    assert "export 20%" in trees.report_line(rows["A"])


def test_report_json(capsys):
    assert trees.main(["--report", "--json", "--tree", "TmlFa4Fwd"]) == 0
    rows = json.loads(capsys.readouterr().out)
    assert rows[-1]["dir"] == "TOTAL" and rows[-1]["tree"] == "TmlFa4Fwd"


def test_report_generated_and_build_log(make_tree, tmp_path):
    tree = make_tree(
        {
            "A/Ref.lean": "-- a\n" * 3,
            "A/Gen/Runs.lean": "-- g\n" * 501,
            "B/X.lean": "-- b\n",
        },
        closed=True,
        generated=["Gen"],
    )
    kgen = tree.kernel_dir / "Gen" / "Step.lean"
    kgen.parent.mkdir()
    kgen.write_text("-- s\n" * 7)
    prefix = tree.module_prefix
    log = tmp_path / "b.log"
    log.write_text(f"✔ [1/2] Built {prefix}A.Gen.Runs (61s)\n✔ [2/2] Built {prefix}B.X (900ms)\n")
    rows = {r["dir"]: r for r in trees.report(tree, log)}
    assert rows["A"]["lines"] == 3 and rows["A"]["generated"] == 501
    assert rows["kernel Gen"]["generated"] == 7 and rows["kernel Gen"]["per_instruction"] is None
    total = rows["TOTAL"]
    assert total["generated"] == 508 and total["over_time"] == 1 and total["over_lines"] == 1
    assert "files >60s 1 >500 lines 1 (b.log)" in trees.report_line(total)
    assert trees.report(tree)[-1]["over_time"] is None


def test_directory_line_ceilings_move_but_never_rise_in_sum(make_tree, monkeypatch):
    tree = make_tree(ceilings={"handwritten lines A": 10, "handwritten lines B": 20})
    old = {"ceilings": {"handwritten lines A": 15, "handwritten lines B": 15}}
    monkeypatch.setattr(tree, "base_config", lambda: old)
    assert tree.ceiling_violations({}) == []
    tree.ceilings["handwritten lines A"] = 11
    assert tree.ceiling_violations({}) == [
        "K: ceiling handwritten lines B raised from 15 to 20",
        "K: the directory line ceilings rose in sum",
    ]

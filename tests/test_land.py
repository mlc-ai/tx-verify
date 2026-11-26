# SPDX-License-Identifier: Apache-2.0
"""Tools/land.py refuses what a lane may not land (synthetic repositories)."""

import subprocess

import land
import pytest

ID = ["-c", "user.name=t", "-c", "user.email=t@t"]


def git(cwd, *args):
    out = subprocess.run(["git", "-C", str(cwd), *ID, *args], check=True, capture_output=True)
    return out.stdout.decode().strip()


@pytest.fixture
def repo(tmp_path, make_tree):
    make_tree(
        {"A/Ref.lean": "theorem a : True := trivial\n", "Top/Correct.lean": ""},
        lanes={"LA": ["A/", "Lemmas/A/"], "LB": ["B/"]},
    )
    for rel in ("Lemmas/A/Old.lean", "Core/X.lean", "Kernels/K/Spec.lean"):
        (tmp_path / rel).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / rel).write_text("-- x\n")
    git(tmp_path, "init", "-q", "-b", "main")
    git(tmp_path, "add", ".")
    git(tmp_path, "commit", "-qm", "base")
    git(tmp_path, "checkout", "-qb", "lane")
    return tmp_path


def commit(repo, files, remove=()):
    for rel, text in files.items():
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text(text)
    for rel in remove:
        (repo / rel).unlink()
    git(repo, "add", "-A")
    git(repo, "commit", "-qm", "work")
    sha = git(repo, "rev-parse", "HEAD")
    git(repo, "checkout", "-q", "main")
    return sha


def landed(repo, sha, capsys, lane="LA"):
    rc = land.land(sha, "K", lane, build=False, root=repo)
    return rc, capsys.readouterr().out


@pytest.mark.parametrize("bad", ["lane", "HEAD", "abc123", "A" * 40, "0" * 39])
def test_refuses_anything_but_a_full_id(repo, capsys, bad):
    rc, out = landed(repo, bad, capsys)
    assert rc == 1 and "not a full 40-hex commit id" in out


@pytest.mark.parametrize(
    "files, remove, lane, why",
    [
        ({"Kernels/K/Proof2/B/X.lean": "-- x\n"}, (), "LA", "outside lane LA"),
        ({"Kernels/K/Proof2/A/X.lean": "-- x\n"}, (), "LC", "lane LC is not"),
        ({"Lemmas/A/Old.lean": "-- edited\n"}, (), "LA", "new files only"),
        ({}, ("Lemmas/A/Old.lean",), "LA", "new files only"),
        ({"Core/X.lean": "-- y\n"}, (), "LA", "outside lane"),
        ({"Kernels/K/Proof2/A/X.lean": "theorem t : 1 = 1 := by sorry\n"}, (), "LA", "sorry"),
        ({"Kernels/K/Proof2/A/X.lean": "axiom ax : False\n"}, (), "LA", "axiom"),
        ({"Kernels/K/Proof2/A/X.lean": "/-- d -/\nprivate axiom ax : False\n"}, (), "LA", "axiom"),
        (
            {"Kernels/K/Proof2/A/X.lean": "example : 1 = 1 := by native_decide\n"},
            (),
            "LA",
            "native",
        ),
    ],
)
def test_refusals(repo, capsys, files, remove, lane, why):
    sha = commit(repo, files, remove)
    rc, out = landed(repo, sha, capsys, lane)
    assert rc == 1 and "refused" in out and why in out, out


def test_frozen_files(repo, capsys, make_tree):
    assert land.FROZEN.match("Core/X.lean")
    assert land.FROZEN.match("Kernels/K/Spec.lean")
    assert land.FROZEN.match("Kernels/K/Theorem.lean")
    assert land.FROZEN.match("Kernels/K/Assumptions/Mem.lean")
    assert land.FROZEN.match("Kernels/K/AssumptionsExtra.lean")
    assert land.FROZEN.match("lakefile.lean")
    assert not land.FROZEN.match("Kernels/K/Proof2/A/SpecLike.lean")
    with pytest.raises(land.Refused):
        land.check_frozen([("M", "Kernels/K/Spec.lean")])


def test_comments_are_not_forbidden(repo, capsys):
    text = (
        "-- no sorry here\n/- axiom -/\n/-- An axiom-free proof; /- nested sorry -/ no axiom. -/\n"
        'theorem axiom_free : True := trivial\ndef s := "sorry, axiom"\n'
    )
    sha = commit(repo, {"Kernels/K/Proof2/A/X.lean": text})
    rc, out = landed(repo, sha, capsys)
    assert "no sorry, native_decide, axiom: ok" in out


def test_a_failing_static_test_aborts_the_merge(repo, capsys):
    """The synthetic repository has no tests: the static tests fail and the merge is undone."""
    head = git(repo, "rev-parse", "HEAD")
    sha = commit(repo, {"Kernels/K/Proof2/A/X.lean": "theorem x : True := trivial\n"})
    rc, out = landed(repo, sha, capsys)
    assert rc == 1 and "static tests: FAILED" in out and "merge aborted" in out
    assert git(repo, "rev-parse", "HEAD") == head
    assert git(repo, "status", "--porcelain") == ""


def test_module_list(repo, make_tree):
    changed = [
        ("A", "Lemmas/X.lean"),
        ("M", "Kernels/K/Proof2/A/B.lean"),
        ("D", "Lemmas/Y.lean"),
        ("A", "Tools/x.py"),
        ("M", "lakefile.lean"),
        ("A", "Tests/Gen/Z.lean"),
    ]
    assert land.lean_modules(changed, repo) == [
        "Kernels.K.Proof2.A.B",
        "Lemmas.X",
        "Tests.Gen.Z",
    ]
    ts = land.trees.load(None, repo)
    mods, tops = land.build_targets(ts, changed, repo)
    # the changed modules, the top module of every open tree, then every other module of the tree
    assert mods[:4] == [
        "Kernels.K.Proof2.A.B",
        "Lemmas.X",
        "Tests.Gen.Z",
        "Kernels.K.Proof2.Top.Correct",
    ]
    assert len(mods) == len(set(mods))
    assert all(m.startswith("Kernels.K.Proof2.") for m in mods[4:])
    assert [t.kernel for t in tops] == ["K"]


def test_without_tree(repo, capsys):
    """Without `--tree` a path is checked against the lane's paths in every tree."""
    sha = commit(repo, {"Kernels/K/Proof2/B/X.lean": "-- x\n"})
    rc = land.land(sha, None, "LA", build=False, root=repo)
    out = capsys.readouterr().out
    assert rc == 1 and "outside lane LA" in out
    sha = commit(repo, {"Kernels/K/Proof2/A/Y.lean": "-- y\n"})
    rc = land.land(sha, None, "LZ", build=False, root=repo)
    assert rc == 1 and "lane LZ is not in" in capsys.readouterr().out

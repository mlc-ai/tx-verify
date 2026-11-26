# SPDX-License-Identifier: Apache-2.0
"""Tools/check_times.py: file check times stay under their ceilings, robust to a loaded machine."""

import json
import os
import warnings

import check_times as ct
import pytest
import trees

# Where a table lived before it moved to `Kernels/<K>/check_times.json`.
LEGACY = {"TmlFa4Fwd": "Tools/check_times.json"}


QUIET = {"start": 1.0, "end": 2.0, "cores": 100}
LOADED = {"start": 1.0, "end": 60.0, "cores": 100}


def log(path, mtime, lines, hashes=None, load=None):
    path.write_text("".join(f"Built {m} ({t}s)\n" for m, t in lines))
    os.utime(path, (mtime, mtime))
    if hashes is not None:
        ct.hashes_path(path).write_text(json.dumps({"load": load, "hashes": hashes}))
    return path


def test_quiet_is_low_load(monkeypatch):
    monkeypatch.delenv("TXVERIFY_QUIET_LOAD", raising=False)
    assert ct.is_quiet(QUIET)
    assert ct.is_quiet({"start": 15.0, "end": 1.0, "cores": 100})
    assert not ct.is_quiet({"start": 15.1, "end": 1.0, "cores": 100})
    assert not ct.is_quiet(LOADED)
    assert not ct.is_quiet(None)
    assert not ct.is_quiet({"start": 1.0, "cores": 100})
    monkeypatch.setenv("TXVERIFY_QUIET_LOAD", "0.5")
    assert not ct.is_quiet(QUIET)


def test_verdict_counts_quiet_logs_only(make_tree):
    tree = make_tree(check_limit=15.0)
    p = tree.module_prefix
    times = {
        p + "A": [(100.0, True)],  # over 1.5 x 60 in a quiet log: fails
        p + "B": [(100.0, False), (100.0, False)],  # over in loaded logs only: deferred
        p + "C": [(30.0, False), (30.0, True)],  # over 1.5 x 15 in the newest quiet log: fails
        p + "D": [(400.0, False), (14.0, True)],  # within it in the quiet log: passes
        p + "H": [(20.0, True), (400.0, True)],  # the newest quiet log decides: passes
        p + "I": [(22.0, False)],  # within 1.5 x 15 even loaded: neither
        p + "Gen.E": [(400.0, True)],  # generated: not checked
        "Other.F": [(400.0, True)],  # not in the tree
    }
    failed, deferred = ct.verdict(tree, times, {p + "A": 60.0, p + "B": 60.0})
    assert set(failed) == {p + "A", p + "C"}
    assert set(deferred) == {p + "B"}


def test_unmeasured(make_tree):
    tree = make_tree({"A/X.lean": "", "A/Y.lean": "", "Gen/G.lean": ""})
    p = tree.module_prefix
    times = {p + "A.X": [(1.0, False), (1.0, True)], p + "A.Y": [(1.0, False)]}
    assert ct.unmeasured(tree, times) == [p + "A.Y"]


def test_lowered(make_tree):
    tree = make_tree(check_limit=15.0)
    p = tree.module_prefix
    times = {p + "A": [(100.0, True), (120.0, False)], p + "B": [(29.0, False)]}
    table = {p + "A": 120.0, p + "B": 20.0, p + "E": 10.0}
    assert ct.lowered(tree, times, table) == {p + "A": 100.0, p + "B": 20.0}


def test_a_log_counts_for_the_text_it_built(tmp_path):
    src = tmp_path / "Kernels/K/A.lean"
    src.parent.mkdir(parents=True)
    src.write_text("old")
    os.utime(src, (1000, 1000))
    logs = tmp_path / "logs"
    logs.mkdir()
    # By mtime: a log older than the file does not count; without a load record it is loaded.
    log(logs / "1.log", 500, [("Kernels.K.A", 9)])
    log(logs / "2.log", 2000, [("Kernels.K.A", 7)])
    # By hash: a log that recorded another text does not count, whatever its time.
    log(logs / "3.log", 3000, [("Kernels.K.A", 5)], {"Kernels.K.A": "0" * 40}, QUIET)
    log(logs / "4.log", 4000, [("Kernels.K.A", 3)], {"Kernels.K.A": ct.sha1(src)}, QUIET)
    log(logs / "5.log", 5000, [("Kernels.K.A", 4)], {"Kernels.K.A": ct.sha1(src)}, LOADED)
    # An old record: hashes only, no load.
    log(logs / "6.log", 6000, [("Kernels.K.A", 2)])
    ct.hashes_path(logs / "6.log").write_text(json.dumps({"Kernels.K.A": ct.sha1(src)}))
    assert ct.current_times(ct.log_files(logs), root=tmp_path) == {
        "Kernels.K.A": [(2.0, False), (4.0, False), (3.0, True), (7.0, False)]
    }


def test_record_drops_a_file_edited_during_the_build(tmp_path):
    for name in ("A", "B"):
        (tmp_path / "Kernels/K").mkdir(parents=True, exist_ok=True)
        (tmp_path / f"Kernels/K/{name}.lean").write_text(name)
    path = tmp_path / "x.log"
    ct.record_start(path, tmp_path)
    (tmp_path / "Kernels/K/B.lean").write_text("edited")
    path.write_text("Built Kernels.K.A (1s)\nBuilt Kernels.K.B (2.5ms)\n")
    ct.record(path, tmp_path)
    hashes, load = ct.read_record(path)
    assert set(hashes) == {"Kernels.K.A"}
    assert set(load) == {"start", "end", "cores"} and load["cores"] == os.cpu_count()
    assert ct.built(path) == [("Kernels.K.A", 1.0), ("Kernels.K.B", 0.0025)]


def test_confirm_refuses_on_a_loaded_machine(monkeypatch, tmp_path):
    monkeypatch.setenv("TXVERIFY_QUIET_LOAD", "-1")
    assert ct.confirm({"Kernels.K.A"}, root=tmp_path) is None


def test_no_file_is_over_its_ceiling(tree):
    logs = ct.log_files()
    if not logs:
        pytest.skip("no build logs")
    failed, deferred = ct.verdict(tree, ct.current_times(logs), ct.ceilings(tree))
    if deferred:
        warnings.warn(
            f"{tree.kernel}: {len(deferred)} files over their ceilings in loaded logs only "
            f"(deferred; Tools/check_times.py --tree {tree.kernel} --deferred)",
            stacklevel=1,
        )
    assert not failed, f"seconds and ceiling: {failed}; deferred: {len(deferred)}"


def test_ceilings_do_not_rise(tree):
    table = ct.ceilings(tree)
    base = trees.merge_base(tree.repo)
    rel = ct.table_path(tree).relative_to(tree.repo).as_posix()
    old = trees.show_json(base, rel, tree.repo)
    if old is None and tree.kernel in LEGACY:
        old = trees.show_json(base, LEGACY[tree.kernel], tree.repo)
    if old is None:
        return
    old_limit = (tree.base_config() or {}).get("check_limit", tree.check_limit)
    assert tree.check_limit <= old_limit
    risen = {m: (c, old.get(m, old_limit)) for m, c in table.items() if c > old.get(m, old_limit)}
    assert not risen, f"ceiling: (now, merge base) {risen}"

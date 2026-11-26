# SPDX-License-Identifier: Apache-2.0
"""Shared fixtures: `Tools/` on the import path, the proof trees, and synthetic trees."""

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "Tools") not in sys.path:
    sys.path.insert(0, str(ROOT / "Tools"))

import trees  # noqa: E402

TREES = trees.load()


def pytest_generate_tests(metafunc):
    """A test with a `tree` argument runs once per tree (`Kernels/*/tree.json`)."""
    if "tree" in metafunc.fixturenames:
        metafunc.parametrize("tree", TREES, ids=[t.kernel for t in TREES])


def minimal_config(**over):
    cfg = {
        "kernel": "K",
        "instructions": 10,
        "root": "Kernels/K/Proof2",
        "namespace": "PTX.Kernels.K.Proof2",
        "old_roots": ["Kernels/K/Proof"],
        "roles": {"A": [], "B": []},
        "common": "Common",
        "lower": ["Iface", "Lib"],
        "upper": ["Protocol", "Top"],
        "generated": ["Gen"],
        "state_names": ["stateAt", "\\.D\\b", "\\bSite\\b", "\\bRef[A-Z]?\\w*"],
        "top": {"correct": "Top/Correct.lean", "theorem": "correct", "open": "Top/Open.lean"},
        "closed": False,
        "ceilings": {},
        "premises": {},
        "iface": {},
        "lanes": {"LA": ["A/"], "LB": ["B/", "Lemmas/Extra/"], "L": ["Lemmas/", "Tools/"]},
    }
    cfg.update(over)
    return cfg


@pytest.fixture
def make_tree(tmp_path):
    """`make_tree(files, **config)`: a tree `K` in a fresh directory, with `files` (paths
    relative to the tree's root) written."""

    def make(files=None, **over):
        cfg = minimal_config(**over)
        kdir = tmp_path / "Kernels" / cfg["kernel"]
        kdir.mkdir(parents=True, exist_ok=True)
        (kdir / "tree.json").write_text(json.dumps(cfg, indent=2))
        root = tmp_path / cfg["root"]
        for rel, text in (files or {}).items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return trees.Tree(kdir / "tree.json", tmp_path)

    return make

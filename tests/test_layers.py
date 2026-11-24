# SPDX-License-Identifier: Apache-2.0
"""Layering of tml-fa4's Proof (Tools/layers.py): the counters' ceilings."""

import importlib
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

# They may fall, not rise; a commit that lowers one lowers its number here.
MAY_NOT_RISE = {
    "upper imports of role internals": 177,
    "imports between roles": 0,
    "upper import all": 1,
    "upper names of role invariants": 293,
    "upper case splits on the role": 76,
}


@pytest.fixture
def layers(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT / "Tools"))
    return importlib.import_module("layers")


def test_definitions(layers, tmp_path):
    (tmp_path / "Top").mkdir()
    (tmp_path / "Mma").mkdir()
    p = "Kernels.TmlFa4Fwd.Proof."
    (tmp_path / "Top/A.lean").write_text(
        f"import {p}Mma.Ref\nimport {p}Mma.Export.Bar\nimport all {p}Top.JR\n"
        "/- JR_eq -/\nrw [JR_eq]\ncases i with\n-- Mma.Ref\n"
    )
    (tmp_path / "Mma/B.lean").write_text(f"import {p}Loader.Ref\nimport {p}Startup.Machine\n")
    assert [len(v) for v in layers.counters(tmp_path).values()] == [1, 1, 1, 1, 1]


def test_counters_do_not_rise(layers):
    now = {k: len(v) for k, v in layers.counters().items()}
    assert set(now) == set(MAY_NOT_RISE)
    risen = {k: (n, MAY_NOT_RISE[k]) for k, n in now.items() if n > MAY_NOT_RISE[k]}
    assert not risen, f"counter: (now, ceiling) {risen}"

# SPDX-License-Identifier: Apache-2.0
"""Tools/check_times.py: file check times stay under their ceilings."""

import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent


@pytest.fixture(scope="module")
def ct():
    spec = importlib.util.spec_from_file_location("check_times", ROOT / "Tools/check_times.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_over_and_lowered(ct):
    p = ct.PREFIX
    times = {p + "A": 100.0, p + "B": 29.0, p + "C": 31.0, p + "Gen.D": 400.0, "Other": 400.0}
    assert set(ct.over(times, {p + "A": 60.0})) == {p + "C"}
    assert ct.lowered(times, {p + "A": 120.0, p + "B": 20.0, p + "E": 10.0}) == {
        p + "A": 100.0,
        p + "B": 20.0,
    }


def test_no_file_is_over_its_ceiling(ct):
    logs = list((ROOT / ".lake/build-logs").glob("*.log"))
    if not logs:
        pytest.skip("no build logs")
    slow = ct.over(ct.newest_times(logs), json.loads(ct.TABLE.read_text()))
    assert not slow, f"seconds and ceiling: {slow}"

# SPDX-License-Identifier: Apache-2.0
"""The reading-disclosure check in Tools/reading_uses.py."""

import importlib
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parents[1] / "Tools"


@pytest.fixture
def ru(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("reading_uses")


def test_sentence_every_kernel(ru):
    alts, kernels = ru.parse_sentence("Disclosed by every kernel: A, B.")
    assert alts is None and kernels == ["A", "B"]


def test_sentence_condition(ru):
    s = (
        "Disclosed by every kernel whose statement names `Op.a`, `Op.b (uni := true)` or "
        "`Op.c` and `Op.d (aOff ≠ 0)`: none."
    )
    alts, kernels = ru.parse_sentence(s)
    assert kernels == []
    assert [[a.key() for a in alt] for alt in alts] == [
        [("Op.a", None, False, None)],
        [("Op.b", "uni", True, "true")],
        [("Op.c", None, False, None), ("Op.d", "aOff", False, "0")],
    ]


@pytest.mark.parametrize(
    "bad",
    [
        "Disclosed by every kernel whose proof uses it (A).",
        "Disclosed by every kernel whose statement names Op.a: A.",
        "Disclosed by every kernel: A",
    ],
)
def test_sentence_rejects(ru, bad):
    with pytest.raises(ValueError):
        ru.parse_sentence(bad)


def test_sentence_round_trip(ru):
    s = "Disclosed by every kernel whose statement names `Op.a (x := true)` or `Op.b`: K."
    alts, kernels = ru.parse_sentence(s)
    note = ru.Note("EXT-X", Path("x"), (0, 0), alts, kernels)
    assert " ".join(ru.sentence(note, kernels)) == s


NOTE = """/-!
### EXT-X — an example note

Statement: A reading.

Effect: If the hardware differs, the result differs. Disclosed
  by every kernel whose statement names `Op.a (mode :=
  M.b)` or `Op.c`: K1, K2. -/
"""


def test_sentence_inside_effect(ru, monkeypatch, tmp_path):
    (tmp_path / "Core").mkdir()
    (tmp_path / "Core/README.md").write_text("")
    path = tmp_path / "Core/X.lean"
    path.write_text(NOTE)
    monkeypatch.setattr(ru, "ROOT", tmp_path)
    found, errors = ru.notes()
    assert errors == [] and len(found) == 1
    note = found[0]
    assert note.kernels == ["K1", "K2"]
    assert [[a.key() for a in alt] for alt in note.alternatives] == [
        [("Op.a", "mode", True, "M.b")],
        [("Op.c", None, False, None)],
    ]
    monkeypatch.setattr(ru, "computed", lambda n, ks, hits: {"K1"})
    ru.write(found, ["K1", "K2"], None)
    lines = path.read_text().splitlines()
    assert lines[5:] == [
        "Effect: If the hardware differs, the result differs. Disclosed by every kernel whose "
        "statement names",
        "  `Op.a (mode := M.b)` or `Op.c`: K1. -/",
    ]


def test_disclosures_match_theorem_lists():
    run = subprocess.run(
        [sys.executable, str(TOOLS / "reading_uses.py")], capture_output=True, text=True
    )
    assert run.returncode == 0, run.stdout + run.stderr


@pytest.mark.skipif(not os.environ.get("TXVERIFY_BUILD"), reason="set TXVERIFY_BUILD=1 (slow)")
def test_disclosures_match_statements():
    if shutil.which("lake") is None and not (Path.home() / ".elan/bin/lake").exists():
        pytest.skip("lake unavailable")
    run = subprocess.run(
        [sys.executable, str(TOOLS / "reading_uses.py"), "--lean"], capture_output=True, text=True
    )
    assert run.returncode == 0, run.stdout + run.stderr


def test_kernel_local_disclosure_register(ru, monkeypatch, tmp_path):
    (tmp_path / "Core").mkdir()
    path = tmp_path / "Core" / "README.md"
    path.write_text(
        "### EXT-X — shared reading\n\n"
        "Disclosed by every kernel whose statement names `Op.a`: Legacy.\n"
    )
    for name in ("Legacy", "Local"):
        directory = tmp_path / "Kernels" / name
        directory.mkdir(parents=True)
        (directory / "Theorem.lean").write_text(
            "/-!\n## Readings this result depends on\n\n- EXT-X.\n-/\n"
        )
    registry = tmp_path / "Kernels/Local/READINGS.md"
    ru.write_registry(registry, {"EXT-X"})
    monkeypatch.setattr(ru, "ROOT", tmp_path)
    monkeypatch.setattr(sys, "argv", ["reading_uses.py", "--lean", "--write"])
    monkeypatch.setattr(
        ru, "lean_hits", lambda kernels, atoms: {k: {atoms[0].key(): True} for k in kernels}
    )
    ru.main()
    assert "Legacy." in path.read_text() and "Local" not in path.read_text()
    assert registry.read_text() == "# EXT disclosures\n\n- EXT-X\n"

    monkeypatch.setattr(sys, "argv", ["reading_uses.py", "--lean"])
    registry.write_text("# EXT disclosures\n\n")
    with pytest.raises(SystemExit, match="1"):
        ru.main()

# SPDX-License-Identifier: Apache-2.0
"""The quote and Lean text checkers in Tools/."""

import importlib
import os
import subprocess
import sys
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parents[1] / "Tools"
SPEC = os.environ.get("TXVERIFY_PTX_SPEC")


@pytest.fixture
def text(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("check_lean_text")


@pytest.fixture
def quotes(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("check_quotes")


def messages(text, src, **kw):
    return [m for _, m in text.check(Path("x.lean"), src, **kw)]


def test_text_accepts_clean_file(text):
    assert messages(text, "def a := 1\n") == []


def test_text_whitespace_and_newline(text):
    assert messages(text, "def a := 1 \n") == ["trailing whitespace"]
    assert "file must end with exactly one newline" in messages(text, "def a := 1")
    assert "file must end with exactly one newline" in messages(text, "def a := 1\n\n")


def test_text_forbidden_words_only_in_code(text):
    ok = '-- sorry\n/-- admit and\nnative_decide -/\ndef s := "sorry axiom"\ndef c := \'"\'\n'
    assert messages(text, ok) == []
    assert messages(text, "theorem t : True := by sorry\n") == ["forbidden `sorry` in code"]
    assert messages(text, "example : True := by native_decide\n")
    assert messages(text, "axiom foo : False\n") == ["`axiom` declaration"]
    assert messages(text, "private axiom foo : False\n") == ["`axiom` declaration"]


def test_text_width_is_opt_in(text):
    src = "def a := " + "x" * 120 + "\n"
    assert messages(text, src) == []
    assert len(messages(text, src, max_width=100)) == 1


def test_quotes_skipped_without_spec():
    env = {k: v for k, v in os.environ.items() if k != "TXVERIFY_PTX_SPEC"}
    run = subprocess.run(
        [sys.executable, str(TOOLS / "check_quotes.py")], env=env, capture_output=True, text=True
    )
    assert run.returncode == 0 and "skipped: no spec text" in run.stdout


def test_quotes_strict(quotes, tmp_path):
    f = tmp_path / "A.lean"
    f.write_text('/-- "must be  exactly here" and "something [...] not there" -/\n')
    ok, missing = quotes.check("A thing  that must be exactly here, then more.", [f])
    assert ok == 1 and [q for _, q in missing] == ["something [...] not there"]


@pytest.mark.skipif(not SPEC, reason="set TXVERIFY_PTX_SPEC to the PTX ISA text")
def test_core_quotes_are_verbatim():
    run = subprocess.run(
        [sys.executable, str(TOOLS / "check_quotes.py"), "--spec", SPEC],
        capture_output=True,
        text=True,
    )
    assert run.returncode == 0, run.stdout


def test_text_width_exemptions(text):
    long = "-- " + "x" * 120 + "\n"
    assert len(messages(text, long, max_width=100)) == 1
    assert messages(text, "-- http://example.org/" + "x" * 120 + "\n", max_width=100) == []
    exempt = "set_option linter.style.longLine false\n" + long
    assert messages(text, exempt, max_width=100) == []


def test_text_string_gap_is_one_literal(text):
    assert messages(text, 'def a := "sor\\\nry"\n') == []
    assert messages(text, 'def a := "x\\\n  sorry"\n') == []


@pytest.fixture
def wrapper(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("lean_wrap")


@pytest.mark.parametrize(
    "line,step",
    [
        (
            '    .instruction none "ld" ['
            + ", ".join(f'(.register "%r{i}")' for i in range(30))
            + "],",
            2,
        ),
        (
            "theorem t : K.code[7]? = some ⟨none, "
            + " ".join(f"(.reg {i})" for i in range(40))
            + "⟩ := by",
            4,
        ),
        ("def live : List Nat := [" + ", ".join(str(i) for i in range(200)) + "]", 4),
        ("def k : Array Nat := #[" + ", ".join(f"n_{i}" for i in range(60)) + "]", 4),
        ("  { guard := none, op := " + " ".join(f"(A.b {i})" for i in range(40)) + " },", 2),
    ],
)
def test_wrap_only_changes_white_space(wrapper, line, step):
    out = wrapper.wrap(line, step)
    assert "".join(out.split()) == "".join(line.split())
    assert all(len(x) <= wrapper.WIDTH for x in out.split("\n"))


def test_wrap_breaks_a_long_string_with_gaps(wrapper):
    name = "a" * 180
    out = wrapper.wrap(f'    .instruction none "{name}" [(.register "%r1")],', 2)
    assert all(len(x) <= wrapper.WIDTH for x in out.split("\n"))
    # a string gap `\` + newline + white space contributes nothing to the value
    value = out.replace("\\\n", "")
    assert "".join(value.split()) == f'.instructionnone"{name}"[(.register"%r1")],'


def test_no_local_paths():
    """No tracked file names a machine-local absolute path (Tools/check_local_paths.py)."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "check_local_paths", Path(__file__).resolve().parents[1] / "Tools" / "check_local_paths.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert mod.offending(mod.tracked()) == []
    sample = "see " + "/" + "home/user/x"
    assert mod.PATTERN.search(sample) and not mod.PATTERN.search("a/home/b")

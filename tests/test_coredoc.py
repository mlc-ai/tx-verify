# SPDX-License-Identifier: Apache-2.0
"""The reader document generator in Tools/coredoc.py."""

import importlib
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture
def coredoc(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT / "Tools"))
    return importlib.import_module("coredoc")


def test_coredoc_is_fresh():
    """docs/core is current, every contract block of Core is in exactly one chapter, every
    `Defs` name resolves and every chapter concept has a doc comment."""
    result = subprocess.run(
        [sys.executable, str(ROOT / "Tools" / "coredoc.py"), "--check"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_declarations_are_named_as_lean_names_them(coredoc):
    src = "\n".join(
        [
            "namespace PTX",
            "@[expose] public section",
            "namespace Decode",
            "/-- A doc. -/",
            "@[simp] def first (n : Nat) : Nat := n",
            "",
            "@[reducible]",
            "def second : Nat := helper",
            "where",
            "  /-- The helper. -/",
            "  helper : Nat := 1",
            "end Decode",
            "def _root_.PTX.Event.counts : Bool := true",
            "end",
            "end PTX",
        ]
    )
    decls = {d.name: d for d in coredoc.parse_decls("x.lean", src)}
    assert decls["PTX.Decode.first"].doc == "A doc."
    assert decls["PTX.Decode.first"].start == 4
    assert "PTX.Decode.second" in decls
    assert decls["PTX.Decode.second.helper"].doc == "The helper."
    assert "PTX.Event.counts" in decls


def test_anchors_distinguish_case(coredoc):
    class Repo:
        comments = {}

    spec = {
        "name": "a",
        "groups": [],
        "concept_groups": [{"name": "g", "items": ["kernel", "Kernel", "Other"]}],
    }
    book = coredoc.Book(Repo(), {"a": spec})
    anchors = [book.anchor[("a", nm)] for nm in ("kernel", "Kernel", "Other")]
    assert len(set(anchors)) == 3
    assert anchors[2] == "c-other"


def test_block_in_two_chapters_is_an_error(coredoc):
    class Repo:
        comments = {"PROG-X": None, "PROG-Y": None}

    spec = {"groups": [{"name": "g", "items": ["PROG-X"]}], "concept_groups": []}
    book = coredoc.Book(Repo(), {"a": spec, "b": spec})
    assert any("PROG-X is in a, b" in e for e in book.errors)
    assert any("PROG-Y is in no chapter" in e for e in book.errors)


def test_rule_id_without_prefix_is_an_error(coredoc):
    text = "/-! ## EXEC-OLD — old\nStatement: s\n-/\n/-! ## MEM-NEW — new\nStatement: s\n-/\n"

    class Repo:
        comments = {c.ident: c for c in coredoc.split_comments("Core/X.lean", text)}

    errors = coredoc.rule_id_errors(Repo())
    assert errors == [
        "Core/X.lean: rule ID EXEC-OLD is not one of the prefixes "
        + ", ".join(coredoc.RULE_PREFIXES)
        + " followed by a hyphenated part, nor CORRECT"
    ]


def test_readme_section_links_names_and_rule_ids(coredoc):
    """A README section links the names of a Core file and rule IDs, and reports a name that
    is not a declaration of that file and an unknown rule ID."""
    repo = coredoc.Repo(ROOT)
    repo.readme = "\n".join(
        [
            "<!-- BEGIN M -->",
            "| `Core/Memory/Order.lean`: `po`, `MSync` | MEM-PROGRAM-ORDER, MEM-NO-SUCH |",
            "<!-- END M -->",
        ]
    )
    spec = {"name": "a", "groups": [], "concept_groups": []}
    book = coredoc.Book(repo, {"a": spec})
    book.errors = []
    lines = coredoc.Chapter(book, "a").readme_section("M")
    assert "[`po`](../../Core/Memory/Order.lean#L" in lines[0]
    assert "[MEM-PROGRAM-ORDER](" in lines[0]
    assert book.errors == [
        "Core/README.md (M): MSync is not a declaration of Core/Memory/Order.lean",
        "Core/README.md (M): no contract block or note MEM-NO-SUCH",
    ]

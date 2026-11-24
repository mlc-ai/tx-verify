# SPDX-License-Identifier: Apache-2.0
"""The contract block layout checker and rewriter, Tools/contract_format.py."""

import importlib
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parents[1] / "Tools"

GOOD = """/-! ## EXT-EXAMPLE — an example block

Statement: Of the lanes of a warp that execute `tcgen05.alloc`, only lane 0 stores the
  returned Tensor Memory address.

Source:
- §9.7.18.7.1: "The store operation in tcgen05.alloc is treated as a weak memory operation"
- §8.6: "Unless otherwise specified, memory operations as defined in Operation types use generic
  method of memory access"
- EXT-OTHER

Direction: reading

Effect: A read of the address by another lane is ordered only by the ordinary memory rules.
-/
"""

OLD = """/-! ## PROG-EXAMPLE — example
Statement: An example rule holds for every example event.
Defs: exampleRule
Source: PTX ISA 9.5 §9.7.1 ("First quote here."); §8.6 ("Second quote.", "Third quote."); EXT-FOO;
  §9.7.2 (a description without a quote)
Direction: equal
Applies: Example events, which
continue unindented here.
Premises: The event exists.
Effect: Execution constraint.

Prose after the fields.
-/
"""


@pytest.fixture
def fmt(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("contract_format")


def rules(fmt, text):
    return sorted({rule for _, _, rule, _ in fmt.check_text(text)})


def test_good_block_has_no_violation(fmt):
    assert list(fmt.check_text(GOOD)) == []


def test_old_block_violations(fmt):
    assert rules(fmt, OLD) == [
        "continuation-indent",
        "field-spacing",
        "source-not-list",
        "unlabeled-paragraph",
    ]


def test_each_rule_alone(fmt):
    glued = GOOD.replace("\n\nDirection", "\nDirection")
    assert rules(fmt, glued) == ["field-spacing"]
    double = GOOD.replace("\n\nDirection", "\n\n\nDirection")
    assert rules(fmt, double) == ["field-spacing"]
    inline = GOOD.replace("Source:\n- ", "Source: ")
    assert "source-not-list" in rules(fmt, inline)
    prose = GOOD.replace("-/", "\nAn unlabeled paragraph.\n-/")
    assert rules(fmt, prose) == ["unlabeled-paragraph"]
    content = GOOD.replace("Direction", "Content: repeats the statement.\n\nDirection")
    assert rules(fmt, content) == ["content-field"]
    unindented = GOOD.replace("  returned Tensor", "returned Tensor")
    assert rules(fmt, unindented) == ["continuation-indent"]
    two = GOOD.replace('operation"', 'operation"; "Another quote"')
    assert rules(fmt, two) == ["source-item-shape"]


def test_note_headings_and_wrapped_heading(fmt):
    text = (
        "/-! ## A-B — first\nStatement: s\n\n### EXT-LONG — a heading that continues\n"
        "  on a second line\n\nStatement: s\n\nSource:\n- EXT-X\n\nDirection: reading\n-/\n"
    )
    assert rules(fmt, text) == []


def test_apply_rewrites_mechanically(fmt):
    new = fmt.rewrite(OLD)
    assert (
        'Source:\n- §9.7.1: "First quote here."\n- §8.6: "Second quote."\n- §8.6: "Third quote."\n'
        "- EXT-FOO\n- §9.7.2 (a description without a quote)\n"
    ) in new
    assert "Applies: Example events, which\n  continue unindented here." in new
    assert rules(fmt, new) == ["unlabeled-paragraph"]
    assert fmt.rewrite(new) == new
    # Only layout changes: the words outside the Source lists stay.
    assert "Prose after the fields." in new


def test_apply_keeps_good_block_and_long_quote_wraps(fmt):
    assert fmt.rewrite(GOOD) == GOOD
    quote = " ".join(["word"] * 60)
    text = f'/-! ## A-B — t\nStatement: s\nSource: §1.2 ("{quote}")\nDirection: equal\n-/\n'
    new = fmt.rewrite(text)
    assert all(len(line) <= 100 for line in new.split("\n"))
    assert " ".join(new.split()).count(quote) == 1


def test_apply_mixed_quote_item_stays_for_a_human(fmt):
    text = '/-! ## A-B — t\nStatement: s\nSource: §1.2 ("q one"; and some text)\nDirection: equal\n-/\n'
    new = fmt.rewrite(text)
    assert rules(fmt, new) == ["source-item-shape"]
    assert fmt.human_source_items(fmt.blocks_of(new.split("\n"))[0]) == [
        '§1.2 ("q one"; and some text)'
    ]


def test_worksheet_lists_content_and_prose(fmt, tmp_path):
    path = tmp_path / "A.lean"
    path.write_text(
        OLD.replace(
            "Direction: equal", "Content: An example rule holds. New fact here.\nDirection: equal"
        )
    )
    sheet = fmt.worksheet([path])
    assert "## PROG-EXAMPLE" in sheet
    assert "New fact here." in sheet
    assert "Unlabeled paragraph" in sheet


def test_index_switch(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    index = importlib.import_module("contract_index")
    assert index.CHECK_FORMAT is True
    sections = list(index.sections(GOOD))
    assert sections[0][2]["Source"].startswith("§9.7.18.7.1:")
    assert "EXT-OTHER" in sections[0][2]["Source"]
    assert list(index.unknown_fields(GOOD, layout=True)) == []

# SPDX-License-Identifier: Apache-2.0
"""The contract field tools: the field check of Tools/contract_index.py and the Guarantee
worksheet of Tools/contract_fields.py."""

import importlib
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parents[1] / "Tools"

BLOCK = """/-! ## PROG-EXAMPLE — example
Statement: An example rule holds for every example event, and its definition is long enough to
  continue on a second line.
Defs: exampleRule
Source: none
Direction: equal
Applies: Example events
Premises: The event exists.
Guarantee: The rule holds, and the empty case is
  allowed.
Effect: Execution constraint.

Prose after the fields.
-/
def exampleRule := 1
"""


@pytest.fixture
def index(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("contract_index")


@pytest.fixture
def fields(monkeypatch, tmp_path):
    monkeypatch.syspath_prepend(str(TOOLS))
    module = importlib.import_module("contract_fields")
    monkeypatch.setattr(module, "ROOT", tmp_path)
    (tmp_path / "Core").mkdir()
    (tmp_path / "Core" / "Example.lean").write_text(BLOCK)
    return module


def test_unknown_field_is_reported(index):
    assert list(index.unknown_fields(BLOCK)) == [("PROG-EXAMPLE — example", "Guarantee")]
    glued = BLOCK.replace("Effect: Execution constraint.\n\n", "Effect: Execution constraint.\n")
    glued = glued.replace("Guarantee: The rule holds, and the empty case is\n  allowed.\n", "")
    glued = glued.replace("Prose after the fields.", "Prose glued to the fields.\nNote: prose.")
    assert list(index.unknown_fields(glued)) == []


def decide(path, fields, decision, new=None, prose=None):
    text = path.read_text().replace("Decision:", f"Decision: {decision}")
    if new:
        text += f"\n{fields.NEW_STATEMENT}:\n\n```text\n{new}\n```\n"
    if prose:
        text += f"\n{fields.PROSE}:\n\n```text\n{prose}\n```\n"
    path.write_text(text)


def test_worksheet_drop(fields, tmp_path):
    sheet = tmp_path / "sheet.md"
    fields.write_worksheet(sheet)
    assert "Guarantee: The rule holds, and the empty case is\n  allowed." in sheet.read_text()
    decide(sheet, fields, "drop")
    fields.apply_worksheet(sheet)
    out = (tmp_path / "Core" / "Example.lean").read_text()
    assert out == BLOCK.replace(
        "Guarantee: The rule holds, and the empty case is\n  allowed.\n", ""
    )


def test_worksheet_merge_with_prose(fields, tmp_path):
    sheet = tmp_path / "sheet.md"
    fields.write_worksheet(sheet)
    decide(
        sheet,
        fields,
        "merge",
        new="An example rule holds, and the empty case is allowed.",
        prose="The empty case is the reading.",
    )
    fields.write_worksheet(sheet)  # refreshing keeps the decision of an unchanged block
    fields.apply_worksheet(sheet)
    out = (tmp_path / "Core" / "Example.lean").read_text()
    assert out.startswith(
        "/-! ## PROG-EXAMPLE — example\n"
        "Statement: An example rule holds, and the empty case is allowed.\nDefs: exampleRule\n"
    )
    assert "Guarantee" not in out
    assert "Effect: Execution constraint.\n\nThe empty case is the reading.\n\nProse after" in out


def test_worksheet_refuses_stale_text(fields, tmp_path):
    sheet = tmp_path / "sheet.md"
    fields.write_worksheet(sheet)
    decide(sheet, fields, "drop")
    src = tmp_path / "Core" / "Example.lean"
    src.write_text(BLOCK.replace("The event exists.", "The event exists twice."))
    with pytest.raises(SystemExit, match="Premises differs"):
        fields.apply_worksheet(sheet)
    assert "Guarantee:" in src.read_text()


def test_worksheet_refuses_missing_decision(fields, tmp_path):
    sheet = tmp_path / "sheet.md"
    fields.write_worksheet(sheet)
    with pytest.raises(SystemExit, match="decision must be drop or merge"):
        fields.apply_worksheet(sheet)


def test_rule_id_prefix_is_checked(index):
    assert list(index.bad_rule_ids(BLOCK)) == []
    for ident in ("THREAD-X", "MEM-X", "OBJ-X", "DEP-X", "ERR-X", "CORRECT", "EXT-X", "ASM-X"):
        assert list(index.bad_rule_ids(BLOCK.replace("PROG-EXAMPLE", ident))) == []
    for ident in (
        "EXEC-EXAMPLE",
        "VALUE-X",
        "PROGRAM-X",
        "prog-x",
        "PROG",
        "MEM",
        "ERR",
        "EXT",
        "CORRECTX",
        "PROG-",
    ):
        assert list(index.bad_rule_ids(BLOCK.replace("PROG-EXAMPLE", ident))) == [ident]


UNSAFE = """def Unsafe (K : Kernel) (X : Execution) : Prop :=
  HasUb X ∨ (∃ a ∈ A, a.ub L X) ∨
    Tmem.Pair.ResourceUnsafe L X ∨ PollShapeUnsafe K X

end
"""


def test_only_err_blocks_own_unsafe_disjuncts(index):
    disjuncts = index.unsafe_disjuncts(UNSAFE)
    assert disjuncts == ["HasUb", "Tmem.Pair.ResourceUnsafe", "PollShapeUnsafe"]
    owner = BLOCK.replace("Defs: exampleRule", "Defs: exampleRule, PollShapeUnsafe")
    assert list(index.unsafe_owners(owner, disjuncts)) == [("PROG-EXAMPLE", "PollShapeUnsafe")]
    for ident in ("DEP-X", "OBJ-X", "MEM-X"):
        assert list(index.unsafe_owners(owner.replace("PROG-EXAMPLE", ident), disjuncts)) == [
            (ident, "PollShapeUnsafe")
        ]
    assert list(index.unsafe_owners(owner.replace("PROG-EXAMPLE", "ERR-X"), disjuncts)) == []
    assert list(index.unsafe_owners(BLOCK, disjuncts)) == []
    assert index.unsafe_disjuncts("def Safe := True\n") == []
    gapped = UNSAFE.replace(" ∨ PollShapeUnsafe", "\n\n    -- a comment\n    ∨ PollShapeUnsafe")
    assert index.unsafe_disjuncts(gapped) == disjuncts
    noted = UNSAFE.replace("Prop :=", "Prop := -- the checks ∨ Note")
    assert index.unsafe_disjuncts(noted) == disjuncts
    with pytest.raises(SystemExit, match="without a definition name"):
        index.unsafe_disjuncts(UNSAFE.replace("HasUb X", "¬ HasUb X"))


def test_unsafe_disjuncts_split_outside_parentheses(index):
    disjuncts = index.unsafe_disjuncts(UNSAFE)
    inner = UNSAFE.replace("(∃ a ∈ A, a.ub L X)", "(∃ a ∈ A, a.ub L X ∨ Foo X)")
    assert index.unsafe_disjuncts(inner) == disjuncts
    grouped = UNSAFE.replace("HasUb X", "HasUb X ∨ (Foo X ∨ 1 < 2)")
    assert index.unsafe_disjuncts(grouped) == disjuncts


def test_unsafe_disjuncts_skip_block_comments_and_raise_on_a_truncated_body(index):
    disjuncts = index.unsafe_disjuncts(UNSAFE)
    leading = UNSAFE.replace(" ∨\n    Tmem", "\n    ∨ Tmem").replace(
        " ∨ PollShapeUnsafe", "\n    ∨ PollShapeUnsafe"
    )
    noted = leading.replace("\n    ∨ Tmem", "\n/- a note -/\n    ∨ Tmem")
    assert index.unsafe_disjuncts(noted) == disjuncts
    nested = leading.replace("\n    ∨ Tmem", "\n/- a /- nested -/\nnote ∨ Foo -/\n    ∨ Tmem")
    assert index.unsafe_disjuncts(nested) == disjuncts
    with pytest.raises(SystemExit, match="no declaration"):
        index.unsafe_disjuncts(UNSAFE.replace("\n    Tmem", "\nnote\n    Tmem"))
    with pytest.raises(SystemExit, match="no declaration"):
        index.unsafe_disjuncts(leading.replace("\n    ∨ Tmem", "\n∨ Tmem"))
    with pytest.raises(SystemExit, match="looks truncated"):
        index.unsafe_disjuncts(UNSAFE.replace("\n    Tmem", "\n/- an open comment\n    Tmem"))


def test_unsafe_owners_match_the_spelling_or_a_qualified_spelling(index):
    disjuncts = index.unsafe_disjuncts(UNSAFE)
    for name in ("Kernel.PollShapeUnsafe", "Pair.ResourceUnsafe", "Foo.HasUb"):
        owner = BLOCK.replace("Defs: exampleRule", f"Defs: exampleRule, {name}")
        assert list(index.unsafe_owners(owner, disjuncts)) == []
    for name in (
        "Tmem.Pair.ResourceUnsafe",
        "PTX.Tmem.Pair.ResourceUnsafe",
        "Core.Tmem.Pair.ResourceUnsafe",
        "PTX.PollShapeUnsafe",
    ):
        owner = BLOCK.replace("Defs: exampleRule", f"Defs: {name}")
        assert list(index.unsafe_owners(owner, disjuncts)) == [("PROG-EXAMPLE", name)]


def test_every_unsafe_disjunct_has_an_err_owner(index):
    disjuncts = index.unsafe_disjuncts(UNSAFE)
    owners = [
        BLOCK.replace("PROG-EXAMPLE", f"ERR-{i}").replace("Defs: exampleRule", f"Defs: {name}")
        for i, name in enumerate(("HasUb", "PTX.Tmem.Pair.ResourceUnsafe", "PollShapeUnsafe"))
    ]
    assert index.unowned_disjuncts(owners, disjuncts) == []
    assert index.unowned_disjuncts(owners[1:], disjuncts) == ["HasUb"]
    prog = owners[0].replace("ERR-0", "PROG-EXAMPLE")
    assert index.unowned_disjuncts([prog] + owners[1:], disjuncts) == ["HasUb"]


def test_lean_contract_prefixes_match_rule_prefixes(index):
    """Tests/Kernel/Contract.lean lists RULE_PREFIXES, then `OPEN` and the prefixes before the rename."""
    text = (TOOLS.parent / "Tests" / "Kernel" / "Contract.lean").read_text()
    body = text.split("meta def prefixes : List String :=", 1)[1].split("]", 1)[0]
    lean = [p.strip().strip('"') for p in body.replace("[", "").split(",")]
    assert "OPEN" in lean, "Tests/Kernel/Contract.lean no longer lists OPEN"
    split = lean.index("OPEN")
    assert lean[:split] == list(index.RULE_PREFIXES)
    assert not set(lean[split + 1 :]) & set(index.RULE_PREFIXES)
    assert len(lean) == len(set(lean))

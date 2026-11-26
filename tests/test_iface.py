# SPDX-License-Identifier: Apache-2.0
"""Tools/iface.py: the cross-lane predicates of each tree agree with their ledger."""

import iface
import pytest

P = "Kernels.K.Proof2."


def header(name, producer="LA", status="row-proved", domain="consistent"):
    return f"-- iface: {name} producer={producer} status={status} domain={domain}\n"


def entry(producer="LA", status="row-proved", domain="consistent"):
    return {"producer": producer, "status": status, "domain": domain}


def test_the_ledger_holds(tree):
    assert iface.problems(tree) == []


GOOD = {
    "Iface/Words.lean": "module\ndef Word := Nat\n",  # vocabulary: no header
    "Iface/Q.lean": header("QArrived")
    + "module\ndef QArrived (X : Execution) (k : Nat) : Prop := X.get k = some e\n",
    "Iface/Out.lean": header("OutDone", "LB", "stated", "complete")
    + "module\ndef OutDone (X : Execution) (hC : Complete l X) : Prop := True\n",
    "Iface/Rows.lean": header("RowsRead", "LB", "proved", "valid-rows")
    + "module\ndef RowsRead (X : Execution) (hValid : RowValid r) : Prop := True\n",
    "B/Use.lean": f"module\nimport {P}Iface.Out\n",
    "A/Use.lean": f"module\nimport {P}Iface.Q\nimport {P}Iface.Rows\n",
}
LEDGER = {
    "QArrived": entry(),
    "OutDone": entry("LB", "stated", "complete"),
    "RowsRead": entry("LB", "proved", "valid-rows"),
}


def test_wrapped_and_old_domain_headers(make_tree):
    files = {
        **GOOD,
        "Iface/Q.lean": "-- SPDX-License-Identifier: Apache-2.0\n"
        "-- iface: QArrived producer=LA status=row-proved\n"
        "--        domain=consistent\n"
        "-- Arrival of Q at a stage.\n"
        "module\ndef QArrived (X : Execution) : Prop := True\n",
        "Iface/Out.lean": "-- domain: complete\n"
        "-- iface: OutDone producer=LB status=stated\n"
        "module\ndef OutDone (X : Execution) (hC : Complete l X) : Prop := True\n",
    }
    assert iface.problems(make_tree(files, iface=LEDGER)) == []
    rows, bad = iface.parse_block(
        ["-- iface: A producer=X status=proved", "--   domain=complete extra"]
    )
    assert rows == [] and len(bad) == 1


def test_a_row_written_ahead(make_tree, capsys):
    """A stated predicate written ahead may be imported by any lane; it stays listed, and
    `--require-proved` fails while it (or any predicate) is below `proved`."""
    use = {"A/Use2.lean": f"module\nimport {P}Iface.Out\n"}
    plain = make_tree({**GOOD, **use}, iface=LEDGER)
    assert any("only stated" in p for p in iface.problems(plain))
    ledger = {**LEDGER, "OutDone": {**LEDGER["OutDone"], "ahead": True}}
    files = {
        **GOOD,
        **use,
        "Iface/Out.lean": header("OutDone", "LB", "stated", "complete").rstrip() + " ahead=1\n"
        "module\ndef OutDone (X : Execution) (hC : Complete l X) : Prop := True\n",
    }
    tree = make_tree(files, iface=ledger)
    assert iface.problems(tree) == []
    assert iface.ahead(tree) == {"OutDone": "stated"}
    assert iface.unproved(tree) == {"OutDone": "stated", "QArrived": "row-proved"}
    # ahead=1 in a header without tree.json's `ahead` is a disagreement
    no_flag = make_tree(files, iface=LEDGER)
    assert any("ahead" in p for p in iface.problems(no_flag))


def test_require_proved(make_tree, monkeypatch, capsys):
    tree = make_tree(GOOD, iface={**LEDGER, "OutDone": {**LEDGER["OutDone"], "ahead": True}})
    monkeypatch.setattr(iface.trees, "load", lambda names=None: [tree])
    assert iface.main(["--ahead"]) == 0
    assert "OutDone  status=stated" in capsys.readouterr().out
    assert iface.main(["--require-proved"]) == 1
    assert "QArrived is row-proved, not proved" in capsys.readouterr().out
    proved = {n: {**e, "status": "proved", "ahead": False} for n, e in LEDGER.items()}
    files = {
        k: v.replace("stated", "proved").replace("row-proved", "proved") for k, v in GOOD.items()
    }
    tree = make_tree(files, iface=proved)
    assert iface.main(["--require-proved"]) == 0


def test_a_consistent_ledger(make_tree):
    assert iface.problems(make_tree(GOOD, iface=LEDGER)) == []


@pytest.mark.parametrize(
    "files, ledger, found",
    [
        # (a) a stated predicate imported outside its producer's paths
        ({"A/Bad.lean": f"module\nimport {P}Iface.Out\n"}, {}, "only stated"),
        # header and tree.json disagree
        ({}, {"QArrived": entry(status="proved")}, "status=row-proved"),
        ({}, {"Missing": entry()}, "has no header"),
        (
            {"Iface/New.lean": header("New") + "def New : Prop := True\n"},
            {},
            "not in tree.json",
        ),
        # (b) domains the definition contradicts
        (
            {
                "Iface/Out.lean": header("OutDone", "LB", "stated", "complete")
                + "def OutDone := 1\n"
            },
            {},
            "without `Complete`",
        ),
        (
            {
                "Iface/Rows.lean": header("RowsRead", "LB", "proved", "valid-rows")
                + "def RowsRead (X : Execution) : Prop := True\n"
            },
            {},
            "without a validity hypothesis",
        ),
        # (c) a word stated as a float
        (
            {
                "Iface/Q.lean": header("QArrived")
                + "def QArrived (w : Word) : Prop := w = .float 1\n"
            },
            {},
            "= .float",
        ),
        ({"Iface/Q.lean": "-- iface: QArrived producer=LA\ndef QArrived := 1\n"}, {}, "malformed"),
        (
            {
                "Iface/Q.lean": header("QArrived").replace("row-proved", "done")
                + "def QArrived := 1\n"
            },
            {},
            "malformed",
        ),
        # an entry after `module` is not in the leading block: the ledger entry has no header
        (
            {"Iface/Q.lean": "module\n" + header("QArrived") + "def QArrived := 1\n"},
            {},
            "no header",
        ),
    ],
)
def test_problems_are_found(make_tree, files, ledger, found):
    tree = make_tree({**GOOD, **files}, iface={**LEDGER, **ledger})
    problems = iface.problems(tree)
    assert any(found in p for p in problems), problems

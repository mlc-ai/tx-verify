# SPDX-License-Identifier: Apache-2.0
"""Completeness checks of the dependency rule (DEP-ORDER, DESIGN-DEPENDENCY §5 items 1 and 5).

The Lean side (oracles, three examples per kind) is Tests/Progress/DependencyCoverage.lean; this file checks
that it exists for every blocking or observing kind, that the classification is total and has no
wildcard (Tools/check_witness.py), and, when the archive checklist and the manual are given
(`TXVERIFY_DEPENDENCY_CHECKLIST`, `TXVERIFY_PTX_SPEC`), that every waiting sentence of the manual is
in the checklist and every checklist quote is verbatim. The mutation run is opt-in
(`TXVERIFY_MUTATION=1`).
"""

import bisect
import importlib
import os
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"
COVERAGE = ROOT / "Tests" / "Progress" / "DependencyCoverage.lean"

# The name that Tests/Progress/DependencyCoverage.lean uses for each blocking or observing kind.
KIND_NAMES = {
    "shfl": "shfl",
    "vote": "vote",
    "voteMode": "voteMode",
    "redux": "redux",
    "match_": "match",
    "elect": "elect",
    "warpBar": "warpBar",
    "matrix": "matrix",
    "setMaxReg": "setMaxReg",
    "bar": "barSync",
    "cluster": "clusterWait",
    "bulkWait": "bulkWait",
    "asyncWait": "asyncWait",
    "wait": "wait",
    "tc.resource": "alloc",
    "tc.ld": "tcLd",
    "tc.st": "tcSt",
    "tc.waitLd": "tcWaitLd",
    "tc.waitSt": "tcWaitSt",
}

# Blocking kinds whose events have two forms with separate examples.
EXTRA_NAMES = ["barArrive", "clusterArrive"]

# Blocking or observing kinds exempt from the coverage requirement, with the EXT reading that
# justifies the exemption. `griddepcontrol.wait` has no event kind: under the single-grid reading
# no prerequisite grid is in flight, so it waits for nothing (EXT-LAUNCH).
EXEMPT = {}

# Free kinds that no checklist row names, with the reason they are free.
FREE_REASON = {
    "rd": "memory layer: a load's value is decided by reads-from (design §4.4)",
    "nc": "memory layer: an `ld.global.nc` read (design §4.4)",
    "wr": "memory layer: a store (design §4.4)",
    "rmw": "memory layer: an atomic decided by reads-from (design §4.4)",
    "exit": "ends the thread; it is a witness of needs, never waits",
    "ub": "undefined behaviour ends the trace",
    "sreg": "reads a special register of the thread (THREAD-SREG)",
    "fence": "a thread fence has memory text only (THREAD-FENCE)",
    "fenceProxy": "a proxy fence has memory text only (THREAD-FENCE)",
    "fenceMbarInit": "memory text only (OBJ-MBAR-INIT-PUBLICATION)",
    "mbInit": "initializes the object; no waiting text (checklist E)",
    "mbInval": "invalidates the object; no waiting text (checklist E)",
    "arrive": "an arrival; no waiting text (checklist E)",
    "asyncArrive": "issue of an asynchronous arrive-on (checklist D)",
    "clcQuery": "decodes a register (design §4.4)",
    "tensorPrefetch": "non-blocking prefetch issue (checklist D13)",
    "tensorIssue": "non-blocking issue (checklist D11)",
    "tensorStore": "non-blocking issue (checklist D11, D12)",
    "copy": "non-blocking issue (checklist D1, D8)",
    "bulkPrefetch": "non-blocking prefetch issue (checklist D10)",
    "bulkCommit": "closes a group (checklist D23)",
    "asyncCommit": "closes a group (checklist D3)",
    "clcIssue": "non-blocking issue (checklist E9)",
    "activemask": "no waiting text (checklist A18)",
    "tc.mma": "asynchronous issue (checklist C17)",
    "tc.commit": "asynchronous issue (checklist C18)",
    "tc.cp": "asynchronous issue (checklist C19)",
    "tc.shift": "asynchronous issue (checklist C20)",
    "tc.fenceBefore": "memory text only (checklist C16)",
    "tc.fenceAfter": "memory text only (checklist C16)",
}


@pytest.fixture
def cw(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("check_witness")


def test_no_wildcard(cw):
    assert cw.check_no_wildcard() == []


def test_classification_total(cw):
    cls, errors = cw.check_kinds()
    assert errors == []
    for k, c in cls.items():
        assert c in ("free", "blocking", "observing"), (k, c)


def test_rules_scan(cw):
    assert cw.check_rules() == []


def test_free_kinds_justified(cw):
    cls, _ = cw.check_kinds()
    for k, c in cls.items():
        if c == "free":
            assert k in FREE_REASON, f"free kind {k} has no reason"


def lean_names():
    text = COVERAGE.read_text()
    return set(re.findall(r"^(?:theorem|example|def|private theorem)\s+([\w.']+)", text, re.M))


def test_coverage_names(cw):
    cls, _ = cw.check_kinds()
    names = lean_names()
    missing = []
    for k, c in cls.items():
        if c == "free" or k in EXEMPT:
            continue
        assert k in KIND_NAMES, f"blocking or observing kind {k} has no coverage name"
        n = KIND_NAMES[k]
        for pre in ("blocks_", "ready_", "witness_other_"):
            if pre + n not in names:
                missing.append(pre + n)
    for n in EXTRA_NAMES:
        for pre in ("blocks_", "ready_", "witness_other_"):
            if pre + n not in names:
                missing.append(pre + n)
    assert missing == []


def test_oracles_exist():
    names = lean_names()
    fams = {n.removeprefix("ready_iff_manual_") for n in names if n.startswith("ready_iff_manual_")}
    wits = {
        n.removeprefix("witness_of_manual_") for n in names if n.startswith("witness_of_manual_")
    }
    assert fams, "no oracle theorems"
    assert fams == wits


SPEC = os.environ.get("TXVERIFY_PTX_SPEC")
CHECKLIST = os.environ.get("TXVERIFY_DEPENDENCY_CHECKLIST")
PATTERN = re.compile(
    r"wait until|waits until|wait till|wait for|waits for|waits on|\bblock\b|\bblocks\b|blocked|"
    r"blocking|unblock|does not return|resum|until all|suspend|potentially blocking|non-blocking|"
    r"stall",
    re.I,
)
# Sections whose matches the checklist excludes ("Excluded grep hits"): thread blocks and basic
# blocks, translation, wgmma and fabric (outside this instruction set), and the matrix data and
# scale-factor blocks.
EXCLUDED_SECTIONS = (
    "1.",
    "2.",
    "3.",
    "6.",
    "11.",
    "12.",
    "13.",
    "14.",
    "9.7.11.",
    "9.7.17",
    "9.7.16.3",
    "9.7.18.4",
    "9.7.18.10.7",
    "9.7.18.10.8",
)
EXCLUDED_START = (
    "Syntax",
    "Examples",
    "Example",
    "Figure",
    "Layout of",
    "Floating-point type",
    "Convolution MMA",
    "Activation Stationary",
    "For example, when N is 0",
    "Block Scaling",
    "Qualifier .block_scale",
    "If .blockN",
    "For more details",
    "The size of the vector",
    "Qualifiers .kind::",
    "Multiply-and-Accumulate",
    "Tensorcore 5th Generation Instructions",
    "The GMEM layout",
    "Wait for completion",
)


def norm(s):
    return re.sub(r"\s+", " ", s)


@pytest.mark.skipif(
    not (SPEC and CHECKLIST), reason="needs TXVERIFY_PTX_SPEC and TXVERIFY_DEPENDENCY_CHECKLIST"
)
def test_checklist_quotes_verbatim():
    t = norm(Path(SPEC).read_text())
    qs = [norm(q) for q in re.findall(r"“([^”]+)”", Path(CHECKLIST).read_text())]
    assert [q for q in qs if q not in t] == []


@pytest.mark.skipif(
    not (SPEC and CHECKLIST), reason="needs TXVERIFY_PTX_SPEC and TXVERIFY_DEPENDENCY_CHECKLIST"
)
def test_checklist_covers_waiting_sentences():
    t = norm(Path(SPEC).read_text())
    qs = [norm(q) for q in re.findall(r"“([^”]+)”", Path(CHECKLIST).read_text())]
    heads = [
        (m.start(), m.group(1))
        for m in re.finditer(r"(?<![\d.])(\d{1,2}(?:\.\d{1,2}){0,5})\. ([^]{1,120}?) ", t)
    ]
    pos = [p for p, _ in heads]
    missing = set()
    for m in PATTERN.finditer(t):
        s = t.rfind(". ", 0, m.start())
        s = 0 if s < 0 else s + 2
        e = t.find(". ", m.end())
        e = len(t) if e < 0 else e + 1
        sent = t[s:e]
        i = bisect.bisect_right(pos, m.start()) - 1
        sec = heads[i][1] + "." if i >= 0 else "?"
        if sec.startswith(EXCLUDED_SECTIONS) or sent.startswith(EXCLUDED_START):
            continue
        if re.search(r"block scal|thread block|blocks of|block size", sent, re.I):
            continue
        if any(q in sent or sent in q for q in qs):
            continue
        missing.add((sec, sent[:200]))
    assert sorted(missing) == []


@pytest.mark.skipif(os.environ.get("TXVERIFY_MUTATION") != "1", reason="TXVERIFY_MUTATION=1")
def test_mutation_run(cw):
    work = os.environ.get("TXVERIFY_MUTATION_DIR")
    assert work, "set TXVERIFY_MUTATION_DIR to a scratch directory"
    res = cw.mutate(work)
    assert [(n, s) for n, s, _ in res if s != "killed"] == []

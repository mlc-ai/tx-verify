# SPDX-License-Identifier: Apache-2.0
"""Checks on kernel proofs.

Two checks apply to every kernel and to the model, because they concern what a theorem can be
trusted for: `Core` imports only `Core` and Mathlib, and no proof contains `sorry` or a new
axiom.

The other checks describe one way of organizing a proof, the layered site-machine style of the
GEMM and FlashAttention-4 proofs, and apply only to the kernels listed in `FRAMEWORK_KERNELS`.
A kernel joins that list by choice. A kernel proved in another style is not listed, and its
proof is constrained only by the trust checks above, by Lean, and by `Tests/Kernel/Statements.lean`.
In the listed kernels, program counters in event form appear only in generated flow tables,
register ids are read only in the thread layer (its value tables and site lemmas), there are no
thread invariants, site machines check fast, layers import lower layers only through the
interface, and `Core` is reached only through the proof library. `Audit/` holds the static
checks of the decoded program, which name registers by nature; nothing in `Proof` imports it.
"""

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
# The kernels whose proofs follow the layered site-machine style and are checked for it.
FRAMEWORK_KERNELS = [
    "Fp16Gemm8192",
    "CopyDynamic",
    "CopyLdg",
    "RowSum",
    "BlockSum",
    "TmaCopy",
    "TcGemm",
    "RmsNorm",
    "AddOne",
    "FlashAttn4Fwd",
    "InklingRelDecode",
]
GEMM = ROOT / "Kernels" / "Fp16Gemm8192"
PROOF = GEMM / "Proof"
PROOFS = [ROOT / "Kernels" / k / "Proof" for k in FRAMEWORK_KERNELS]


def _proof_root(p):
    return next(r for r in PROOFS if r in p.parents)


PC_EVENT = re.compile(r"⟨\d{1,5},\s*\.")
# A register named by its numeric id, in the forms the thread layer reads and writes registers.
REGISTER = re.compile(r"\b(?:regs|readReg\s+\S+|setReg\s+\S+|valueOf(?:\s+\S+){3})\s+\d+\b")
INVARIANT = re.compile(r"^(?:private\s+)?(?:def|structure|inductive|abbrev)\s+Invariant\b", re.M)
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)
MODULE_IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)


def _texts(folder):
    if not folder.exists():
        return {}
    return {p: p.read_text(errors="replace") for p in sorted(folder.rglob("*.lean"))}


def _v2_files():
    return {p: t for r in PROOFS for p, t in _texts(r).items()}


def test_v2_has_no_program_counters_or_register_ids():
    """Program counters appear only in the generated flow tables; register ids only in the
    thread layer."""
    bad = []
    for p, t in _v2_files().items():
        parts = p.relative_to(_proof_root(p)).parts
        patterns = [PC_EVENT] if parts[0] == "Thread" else [PC_EVENT, REGISTER]
        for pattern in patterns:
            for m in pattern.finditer(t):
                bad.append((str(p.relative_to(ROOT)), m.group(0)))
    assert not bad, bad[:20]


def test_v2_defines_no_thread_invariants():
    bad = [str(p.relative_to(ROOT)) for p, t in _v2_files().items() if INVARIANT.search(t)]
    assert not bad, bad


def test_v2_site_machines_check_fast():
    """A rule that keeps the proofs of a site machine fast to check: a transition function
    matches on the site first, so that a known site reduces it without a case split on the
    event. (A local segment is evaluated on its footprint, `seg_fp`; the library has no
    evaluator over every live register.)"""
    slow = re.compile(r"match d\.site, e\.kind with")
    bad = [
        (str(p.relative_to(ROOT)), m.group(0))
        for p, t in _v2_files().items()
        for m in slow.finditer(t)
    ]
    assert not bad, bad[:20]


def test_v2_layers_import_only_interfaces():
    """Protocol and conclusion layers see lower layers only through Interface.lean."""
    order = ["Thread", "Protocol", "Safety", "Progress", "Bound", "Result"]
    # The region layer sits with the protocols: it places the protocols' accesses.
    rank = {name: i for i, name in enumerate(order)} | {"Region": order.index("Protocol")}
    bad = []
    for p, t in _v2_files().items():
        parts = p.relative_to(_proof_root(p)).parts
        if len(parts) < 2 or parts[0] not in rank:
            continue
        layer = rank[parts[0]]
        for m in IMPORT.findall(t):
            prefix = f"Kernels.{_proof_root(p).parent.name}.Proof."
            if not m.startswith(prefix):
                continue
            target = m[len(prefix) :].split(".")
            if target[0] in rank and target[0] != parts[0] and rank[target[0]] < layer:
                if not (target[0] == "Thread" and target[-1] in ("Sites", "Roles")):
                    bad.append((str(p.relative_to(ROOT)), m))
    assert not bad, bad


# What a kernel proof may import: its own kernel's modules (its `Assumptions` included), the
# proof library (with the facts about the assumption constructors in `Lemmas.Assumption.Facts`),
# the tactics and Mathlib. The model (`Core`) and the constructors in
# `Assumption` reach a proof only through the library modules that state lemmas about
# it; the kernel's `Spec`, `Assumptions` and `Theorem` (outside `Proof`) name Core directly.
PROOF_IMPORT_PREFIXES = ("Lemmas.", "Tactics.", "Mathlib.")
# Imports outside those prefixes that a proof file may still use, with the reason.
PROOF_IMPORT_EXEMPT: dict[tuple[str, str], str] = {}


def test_proofs_use_core_only_through_the_library():
    """A kernel proof imports no `Core` module (and no other kernel's modules) directly."""
    bad = []
    for p, t in _v2_files().items():
        kernel = f"Kernels.{_proof_root(p).parent.name}."
        rel = str(p.relative_to(ROOT))
        for m in MODULE_IMPORT.findall(t):
            if m.startswith(PROOF_IMPORT_PREFIXES + (kernel,)):
                continue
            if (rel, m) not in PROOF_IMPORT_EXEMPT:
                bad.append((rel, m))
    assert not bad, bad


@pytest.mark.parametrize(
    ("folder", "allowed"),
    [("Core", ("Core.", "Mathlib.")), ("Assumption", ("Core.", "Assumption.", "Mathlib."))],
)
def test_reviewed_module_imports(folder, allowed):
    """Core stands alone; constructors may import Core and other constructors."""
    bad = []
    for p, t in _texts(ROOT / folder).items():
        for m in MODULE_IMPORT.findall(t):
            if not m.startswith(allowed):
                bad.append((str(p.relative_to(ROOT)), m))
    assert not bad, bad


def test_no_sorry_or_new_axioms_in_proofs():
    bad = []
    for top in ("Lemmas", "Tactics", "Kernels"):
        for p in (ROOT / top).rglob("*.lean"):
            t = p.read_text(errors="replace")
            if re.search(r"\bsorry\b", t) or re.search(r"^\s*axiom\s", t, re.M):
                bad.append(str(p.relative_to(ROOT)))
    assert not bad, bad


# The explicit premises the new proof still assumes. Each must be registered here and in
# `PendingPremises` of Interface.lean; the list must be empty before the switchover.
PENDING_PREMISES: set[str] = set()


def test_v2_pending_premises_registered():
    text = (PROOF / "Interface.lean").read_text()
    if "structure PendingPremises" not in text:
        assert not PENDING_PREMISES
        return
    body = text.split("structure PendingPremises", 1)[1].split("\n\n", 1)[0]
    fields = set(re.findall(r"^  (\w+) :", body, re.M))
    assert fields == PENDING_PREMISES

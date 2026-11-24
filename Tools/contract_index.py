# SPDX-License-Identifier: Apache-2.0
"""Generate the marked rule index in Core/README.md from Core, the assumption constructors in
Core/Assumption included.

Only the marked region is replaced. Each Lean entry names its definitions and evidence;
the Lean contract check validates their ownership and coverage.
"""

import argparse
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import contract_format  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OPENER = "/-! ## "
BEGIN = "<!-- BEGIN CONTRACT INDEX -->"
END = "<!-- END CONTRACT INDEX -->"
FIELDS = ("Statement", "Defs", "Source", "Direction", "Applies", "Premises", "Effect")
# Optional field: reviewer-only material.
OPTIONAL_FIELDS = ("Review",)
FIELD_LINE = re.compile(r"([A-Z][A-Za-z]*): ")
# Every rule ID starts with the prefix of its part of the model: PROG (program, decoding, launch),
# THREAD (single-thread semantics and value encodings), MEM (memory model), OBJ (object state:
# mbarrier, CTA and cluster barriers, bulk async-groups, CLC arbitration, the Tensor Memory
# allocator), DEP (dependency order and asynchronous stages), ERR (Unsafe items), CORRECT
# (correctness), EXT (readings) or ASM (assumptions), followed by at least one hyphenated part.
# The one exception is CORRECT, the top-level correctness statement. Tools/coredoc.py applies the
# same check. Only an ERR block may list a disjunct of `Unsafe` in its Defs (`unsafe_owners`), and
# every disjunct that names a definition has an ERR block (`unowned_disjuncts`).
RULE_PREFIXES = ("PROG", "THREAD", "MEM", "OBJ", "DEP", "ERR", "CORRECT", "EXT", "ASM")
BARE_RULE_IDS = ("CORRECT",)
RULE_ID = re.compile(
    r"(?:" + "|".join(RULE_PREFIXES) + r")(?:-[A-Z0-9]+)+|" + "|".join(BARE_RULE_IDS)
)
# The file of `def Unsafe`, whose disjuncts are the Unsafe items.
UNSAFE_FILE = "Core/Assembly/Execution.lean"
# The layout rules of Tools/contract_format.py (blank lines between fields, a Source list, no
# unlabeled paragraph, no Content field) are enforced when this is True or with `--format`. The
# lead turns it on once every block of Core has the layout.
CHECK_FORMAT = True

# Explicit review order. Coverage is checked against all model modules.
FILES = [
    "Core/Source/Syntax.lean",
    "Core/Source/Isa/Token.lean",
    "Core/Source/Isa/Entry.lean",
    "Core/Source/Isa/Constraint.lean",
    "Core/Source/Isa/Grammar.lean",
    "Core/Isa/Types.lean",
    "Core/Isa/SReg.lean",
    "Core/Source/Operand.lean",
    "Core/Isa/Rule.lean",
    "Core/Isa/Int.lean",
    "Core/Isa/Float.lean",
    "Core/Isa/Move.lean",
    "Core/Isa/Cvt.lean",
    "Core/Isa/Misc.lean",
    "Core/Isa/Fence.lean",
    "Core/Isa/Tc.lean",
    "Core/Isa/Mem.lean",
    "Core/Isa/Warp.lean",
    "Core/Isa/Matrix.lean",
    "Core/Source/Instr.lean",
    "Core/Source/DecodeOps.lean",
    "Core/Source/Decode.lean",
    "Core/Data/Value.lean",
    "Core/Async/Tensor/TensorSwizzle.lean",
    "Core/Async/Tensor/TensorAddress.lean",
    "Core/Async/Tensor/TensorTile.lean",
    "Core/Async/Tensor/TensorDescriptor.lean",
    "Core/Async/Tensor/TensorTransfer.lean",
    "Core/Async/Tensor/TensorCopy.lean",
    "Core/Async/Tensor/TensorMemory.lean",
    "Core/Data/AsyncTypes.lean",
    "Core/Data/Types.lean",
    "Core/Data/TmemPairTypes.lean",
    "Core/Data/Events.lean",
    "Core/Sync/ClusterBarrierObject.lean",
    "Core/Sync/ClusterBarrierHistory.lean",
    "Core/Sync/Cluster.lean",
    "Core/Tmem/CtaPair.lean",
    "Core/Tc/TcCommitTargets.lean",
    "Core/Clc/ClcOwnership.lean",
    "Core/Clc/ClcThread.lean",
    "Core/Clc/ClcEffects.lean",
    "Core/Clc/ClcExecution.lean",
    "Core/Sync/ClusterBarrierExecution.lean",
    "Core/Float/Format.lean",
    "Core/Float/Round.lean",
    "Core/Float/Ieee.lean",
    "Core/Float/Approx.lean",
    "Core/Thread/Float.lean",
    "Core/Thread/Local.lean",
    "Core/Memory/AtomicOp.lean",
    "Core/Thread/Access.lean",
    "Core/Thread/Fence.lean",
    "Core/Sync/CtaBarrierObject.lean",
    "Core/Sync/CtaBarrierHistory.lean",
    "Core/Sync/CtaBarrierExecution.lean",
    "Core/Sync/Barrier.lean",
    "Core/Sync/Shuffle.lean",
    "Core/Sync/WarpInstance.lean",
    "Core/Sync/Vote.lean",
    "Core/Sync/Redux.lean",
    "Core/Sync/Match.lean",
    "Core/Sync/ActiveMask.lean",
    "Core/Sync/Elect.lean",
    "Core/Sync/WarpBarrier.lean",
    "Core/Sync/MatrixLayout.lean",
    "Core/Sync/Matrix.lean",
    "Core/Sync/MatrixExec.lean",
    "Core/Memory/Acquire.lean",
    "Core/Thread/SetMaxNReg.lean",
    "Core/Sync/Aligned.lean",
    "Core/Tc/TcDataAddress.lean",
    "Core/Tc/TcThread.lean",
    "Core/Tc/TcCommitThread.lean",
    "Core/Tc/TcMmaDescriptor.lean",
    "Core/Tc/TcSharedDescriptor.lean",
    "Core/Tc/TcSharedAddress.lean",
    "Core/Tc/TcMmaOperands.lean",
    "Core/Tc/TcMmaResultLayout.lean",
    "Core/Tc/TcMmaCollector.lean",
    "Core/Tmem/TmemObject.lean",
    "Core/Tmem/TmemPair.lean",
    "Core/Tmem/TmemPairRequests.lean",
    "Core/Tmem/AllocResult.lean",
    "Core/Tmem/TmemPairHistory.lean",
    "Core/Tmem/TmemPairCompletion.lean",
    "Core/Tmem/TmemPairRelease.lean",
    "Core/Tmem/TmemPairLifetime.lean",
    "Core/Tc/TcFence.lean",
    "Core/Tc/TcMmaLifetime.lean",
    "Core/Tc/TcPipeline.lean",
    "Core/Tc/TmemStore.lean",
    "Core/Tc/TcCopy.lean",
    "Core/Tc/TcMmaOrder.lean",
    "Core/Tc/TcMmaCompletion.lean",
    "Core/Tc/TcMmaValue.lean",
    "Core/Tc/TcMmaRead.lean",
    "Core/Tc/TcMmaConflicts.lean",
    "Core/Tc/TcMmaSafety.lean",
    "Core/Tc/TcGroup.lean",
    "Core/Tmem/TmemPairAccess.lean",
    "Core/Async/Tma.lean",
    "Core/Async/CpAsync.lean",
    "Core/Async/AsyncStore.lean",
    "Core/Async/CopyForm.lean",
    "Core/Async/Tensor/TensorThread.lean",
    "Core/Async/Tensor/TensorExecution.lean",
    "Core/MBarrier/MBarrierObject.lean",
    "Core/MBarrier/MBarrierHistory.lean",
    "Core/Async/AsyncCopy.lean",
    "Core/Async/BulkGroup.lean",
    "Core/Async/BulkExecution.lean",
    "Core/Async/Tensor/TensorStore.lean",
    "Core/Async/Tensor/TensorStoreMemory.lean",
    "Core/Async/Tensor/TensorReduce.lean",
    "Core/Async/Tensor/TensorAllocation.lean",
    "Core/MBarrier/AsyncMBarrier.lean",
    "Core/Memory/Order.lean",
    "Core/Memory/CommitOperandOrder.lean",
    "Core/Memory/Read.lean",
    "Core/Assembly/SharedLifetime.lean",
    "Core/Tc/TcCommitSafety.lean",
    "Core/Async/Tensor/TensorSafety.lean",
    "Core/Assembly/Safety.lean",
    "Core/Memory/Atomic.lean",
    "Core/Assembly/Waiting.lean",
    "Core/Assembly/WaitOrder.lean",
    "Core/Assembly/PollShape.lean",
    "Core/Assembly/Dependency.lean",
    "Core/MBarrier/InitPublication.lean",
    "Core/Thread/Run.lean",
    "Core/Sync/WarpUniform.lean",
    "Core/Assembly/Execution.lean",
    "Core/Assembly/Progress.lean",
    "Core/Assembly/Correctness.lean",
    "Core/Assumption/NcReadOnly.lean",
    "Core/Assumption/ApproxExact.lean",
    "Core/Assumption/IdealReal.lean",
    "Core/Assumption/ClusterScopeMbar.lean",
    "Core/Assumption/SegmentExact.lean",
    "Core/Assumption/PairEven.lean",
    "Core/Assumption/TcLdDataflow.lean",
    "Core/Assumption/CommitOrder.lean",
    "Core/Assumption/PollAgree.lean",
    "Core/Assumption/SetMaxNRegSync.lean",
]


def sections(text):
    """Yield (id, title, fields) for the numbered module comments."""
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if not line.startswith(OPENER):
            continue
        ident, _, title = line[len(OPENER) :].partition(" — ")
        fields = {}
        previous = None
        for body in lines[i + 1 :]:
            if body.endswith("-/") or body.startswith("### "):
                break
            key, sep, value = body.partition(": ")
            if body.endswith(":") and body[:-1] in FIELDS + OPTIONAL_FIELDS:
                key, sep, value = body[:-1], ":", ""  # a label with a list below it
            if sep and key in FIELDS + OPTIONAL_FIELDS:
                fields[key] = value.strip()
                previous = key
            elif body.startswith("  ") and previous is not None:
                fields[previous] += " " + body.strip()
            elif body.startswith("- ") and previous == "Source":
                # A Source list item; the index shows the items on one line.
                joined = fields[previous] + "; " if fields[previous] else ""
                fields[previous] = joined + body[2:].strip()
            else:
                previous = None
        yield ident.strip(), title.strip(), fields


def bad_rule_ids(text):
    """Yield the ID of each contract block whose ID is not a prefix of RULE_PREFIXES followed by
    at least one hyphenated part, or one of BARE_RULE_IDS."""
    for ident, _, _ in sections(text):
        if not RULE_ID.fullmatch(ident):
            yield ident


DECL_STARTS = (
    "end",
    "def ",
    "theorem ",
    "lemma ",
    "abbrev ",
    "instance ",
    "structure ",
    "inductive ",
    "namespace ",
    "section",
    "open ",
    "variable",
    "noncomputable ",
    "private ",
    "public ",
    "protected ",
    "@[",
    "#",
)


def unsafe_disjuncts(text):
    """The names of the definitions that the disjuncts of `def Unsafe` apply: the first token of
    each disjunct of its body, split at the `∨` outside parentheses, brackets and braces. A
    parenthesized disjunct, such as `(∃ a ∈ A, a.ub ...)`, names no definition and is skipped; any
    other disjunct that does not start with an identifier is an error. The body ends at the first
    line that starts at column 0 outside a comment, which must start a declaration or command
    (`DECL_STARTS`), else the scan raises; a body that
    ends with `∨` or inside a block comment raises, and a body read incompletely therefore raises
    or gives no disjuncts. Blank lines, `--` comments and `/- ... -/` comments (nested) are
    skipped; `--` and `/-` inside a string literal would also be read as comments (the body has
    no string literal)."""
    lines = text.splitlines()
    start = next((i for i, line in enumerate(lines) if line.startswith("def Unsafe ")), None)
    if start is None:
        return []
    body, depth = [], 0
    for k, line in enumerate(lines[start:]):
        lead = line.lstrip()
        if k and not depth and lead and line == lead and not lead.startswith(("--", "/-")):
            if not lead.startswith(DECL_STARTS):
                raise SystemExit(f"a line of `def Unsafe` at column 0 is no declaration: {lead!r}")
            break
        kept, j = [], 0
        while j < len(line):
            if line.startswith("/-", j):
                depth, j = depth + 1, j + 2
            elif depth and line.startswith("-/", j):
                depth, j = depth - 1, j + 2
            elif depth:
                j += 1
            elif line.startswith("--", j):
                break
            else:
                kept.append(line[j])
                j += 1
        body.append("".join(kept))
    _, sep, value = " ".join(body).partition(":=")
    if not sep:
        return []
    if depth or value.rstrip().endswith("∨"):
        raise SystemExit("the body of `def Unsafe` looks truncated")
    parts, level, last = [], 0, 0
    for i, c in enumerate(value):
        if c in "([{":
            level += 1
        elif c in ")]}":
            level = max(level - 1, 0)
        elif c == "∨" and level == 0:
            parts.append(value[last:i])
            last = i + 1
    parts.append(value[last:])
    heads = []
    for disjunct in (p.strip() for p in parts):
        if disjunct.startswith("("):
            continue
        token = disjunct.split(" ")[0]
        if not re.fullmatch(r"[A-Za-z_][\w.]*", token):
            raise SystemExit(f"a disjunct of `def Unsafe` without a definition name: {disjunct!r}")
        heads.append(token)
    return heads


def names_disjunct(name, disjunct):
    """Whether the Defs entry `name` names the disjunct `disjunct` of `def Unsafe`: the same
    spelling, the spelling with `PTX.` in front (Tests/Kernel/Contract.lean resolves a Defs entry `d` as
    `PTX.d` or `d`), or, for a dotted disjunct such as `Tmem.Pair.ResourceUnsafe`, a spelling that
    ends with `.` and the disjunct. An undotted disjunct such as `Race` is matched only by the first
    two, since many definitions of other namespaces end with such a name."""
    return (
        name == disjunct
        or name == "PTX." + disjunct
        or ("." in disjunct and name.endswith("." + disjunct))
    )


def disjunct_owners(text, disjuncts):
    """Yield (id, name, disjunct) for each Defs entry `name` of a contract block that names a
    disjunct of `Unsafe` (`names_disjunct`)."""
    for ident, _, fields in sections(text):
        for name in (d.strip() for d in fields.get("Defs", "").split(",")):
            for disjunct in disjuncts:
                if names_disjunct(name, disjunct):
                    yield ident, name, disjunct


def unsafe_owners(text, disjuncts):
    """Yield (id, name) for a contract block that is not an ERR block and lists a disjunct of
    `Unsafe` in its Defs (`names_disjunct`). The check covers the names of the disjuncts only: a
    predicate that a disjunct uses may belong to any block, and the check does not test where in
    its file a definition stands."""
    for ident, name, _ in disjunct_owners(text, disjuncts):
        if not ident.startswith("ERR-"):
            yield ident, name


def unowned_disjuncts(texts, disjuncts):
    """The disjuncts of `Unsafe` that no ERR block of the texts lists in its Defs."""
    owned = {
        disjunct
        for text in texts
        for ident, _, disjunct in disjunct_owners(text, disjuncts)
        if ident.startswith("ERR-")
    }
    return [d for d in disjuncts if d not in owned]


def unknown_fields(text, layout=False):
    """Yield (heading, key) for a line of a contract block's field lines that has the form of a
    field (`Word: ...`) with a name outside FIELDS and OPTIONAL_FIELDS. The field lines start
    after the heading and end at the first line that is neither a field line nor a continuation
    line (two leading spaces): a blank line, prose, a `### ` note or the closing `-/`.
    With `layout`, blank lines separate the fields, a Source list item belongs to its field, and
    the labels of contract_format.LABELS are known; the field lines end at the first paragraph
    that has no label."""
    known = FIELDS + OPTIONAL_FIELDS + (contract_format.LABELS if layout else ())
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if not line.startswith(OPENER):
            continue
        heading = line[len(OPENER) :].strip()
        for body in lines[i + 1 :]:
            if body.endswith("-/") or body.startswith("### "):
                break
            m = FIELD_LINE.match(body)
            if m:
                if m.group(1) not in known:
                    yield heading, m.group(1)
            elif layout and (not body.strip() or body.startswith("- ")):
                continue
            elif not body.startswith("  "):
                break


def duplicate_fields(text):
    """Yield (heading, field) for a field line that occurs twice in one contract block or
    external/open note."""
    heading, seen = None, set()
    for line in text.splitlines():
        stripped = line.removeprefix("/-! ")
        if stripped.startswith(("## ", "### ")):
            heading, seen = stripped.lstrip("#").strip(), set()
            continue
        if line.endswith("-/") and not line.startswith(" "):
            heading = None
        if heading is None:
            continue
        key, sep, _ = line.partition(": ")
        if line.endswith(":"):
            key, sep = line[:-1], ":"
        if sep and key in FIELDS + OPTIONAL_FIELDS + ("Evidence",):
            if key in seen:
                yield heading, key
            seen.add(key)


def missing_statements(text):
    """Yield the heading of each contract block and EXT/OPEN note without a `Statement:` line.
    A block ends at its closing `-/` or at the next note heading."""
    heading, found = None, False
    for line in text.splitlines() + ["/-! ## end"]:
        stripped = line.removeprefix("/-! ")
        starts = line.startswith(OPENER) or stripped.startswith(("### EXT-", "### OPEN-"))
        if (starts or (line.endswith("-/") and not line.startswith(" "))) and heading:
            if not found:
                yield heading
            heading = None
        if starts:
            heading, found = stripped.lstrip("#").strip(), False
        elif heading and line.startswith("Statement: "):
            found = True


def note_headings(text):
    """External/open notes have one definition, next to their rule or in the guide. A heading
    too long for a line continues on lines that start with two spaces."""
    lines = text.splitlines()
    for i, line in enumerate(lines):
        stripped = line.removeprefix("/-! ")
        if stripped.startswith(("### EXT-", "### OPEN-")):
            heading = stripped[4:]
            for more in lines[i + 1 :]:
                if not more.startswith("  ") or more.endswith("-/"):
                    break
                heading += " " + more.strip()
            yield heading


def render(layout=False):
    """Render the index content, excluding markers and handwritten prose. With `layout`, a
    block that breaks the layout rules of Tools/contract_format.py is an error."""
    found = {str(p.relative_to(ROOT)) for p in (ROOT / "Core").rglob("*.lean")}
    if found != set(FILES) or len(FILES) != len(set(FILES)):
        diff = sorted(found ^ set(FILES))
        raise SystemExit(f"FILES must list exactly the model files once; difference: {diff}")
    dups = [
        f"{f}: {heading}: {key}"
        for f in FILES + ["Core/README.md"]
        for heading, key in duplicate_fields((ROOT / f).read_text())
    ]
    if dups:
        raise SystemExit("duplicate contract fields:\n" + "\n".join(dups))
    bad = [f"{f}: {ident}" for f in FILES for ident in bad_rule_ids((ROOT / f).read_text())]
    if bad:
        raise SystemExit(
            "rule IDs without one of the prefixes "
            + ", ".join(RULE_PREFIXES)
            + ":\n"
            + "\n".join(bad)
        )
    disjuncts = unsafe_disjuncts((ROOT / UNSAFE_FILE).read_text())
    if not disjuncts:
        raise SystemExit(f"no `def Unsafe` with disjuncts in {UNSAFE_FILE}")
    owners = [
        f"{f}: {ident}: {name}"
        for f in FILES
        for ident, name in unsafe_owners((ROOT / f).read_text(), disjuncts)
    ]
    if owners:
        raise SystemExit("disjuncts of Unsafe outside an ERR block:\n" + "\n".join(owners))
    unowned = unowned_disjuncts([(ROOT / f).read_text() for f in FILES], disjuncts)
    if unowned:
        raise SystemExit("disjuncts of Unsafe with no ERR entry: " + ", ".join(unowned))
    unknown = [
        f"{f}: {heading}: {key}"
        for f in FILES
        for heading, key in unknown_fields((ROOT / f).read_text(), layout)
    ]
    if unknown:
        raise SystemExit("unknown contract fields:\n" + "\n".join(unknown))
    # The reader document (Tools/coredoc.py) shows a Statement for every block of Core.
    bare = [f"{f}: {h}" for f in FILES for h in missing_statements((ROOT / f).read_text())]
    if bare:
        raise SystemExit("contract blocks without a Statement:\n" + "\n".join(bare))
    if layout:
        messages, _, _ = contract_format.check_files([ROOT / f for f in FILES])
        if messages:
            raise SystemExit("contract block layout:\n" + "\n".join(messages))
    out = [
        "Generated by `Tools/contract_index.py`; edit the entries beside the Lean definitions.",
        "Directions are explained [above](#directions).",
        "",
    ]
    for f in FILES:
        text = (ROOT / f).read_text()
        link = Path(os.path.relpath(ROOT / f, ROOT / "Core")).as_posix()
        out += [
            f"### [{f}]({link})",
            "",
            "| ID | Entry | Definitions | Source | Direction |",
        ]
        out += ["| --- | --- | --- | --- | --- |"]
        for ident, title, fields in sections(text):
            defs = ", ".join(f"`{d.strip()}`" for d in fields.get("Defs", "").split(","))
            cells = [
                ident,
                title,
                defs,
                fields.get("Source", ""),
                fields.get("Direction", ""),
            ]
            out.append("| " + " | ".join(c.replace("|", "\\|") for c in cells) + " |")
        for note in note_headings(text):
            out.append(f"\nReview note: [{note}]({link}).")
        out.append("")
    return "\n".join(out).rstrip() + "\n"


def replace_index(text, index):
    """Replace exactly one ordered marker pair, preserving all other bytes."""
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise ValueError("Core/README.md needs exactly one BEGIN/END CONTRACT INDEX pair")
    before, rest = text.split(BEGIN)
    if END in before:
        raise ValueError("CONTRACT INDEX markers are reversed")
    _, after = rest.split(END)
    return before + BEGIN + "\n" + index.rstrip() + "\n" + END + after


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the README index is stale")
    parser.add_argument(
        "--format", action="store_true", help="also check the block layout (see CHECK_FORMAT)"
    )
    args = parser.parse_args()
    path = ROOT / "Core/README.md"
    old = path.read_text()
    try:
        new = replace_index(old, render(args.format or CHECK_FORMAT))
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    if args.check:
        if old != new:
            raise SystemExit("Core/README.md index is stale: run Tools/contract_index.py")
    else:
        path.write_text(new)


if __name__ == "__main__":
    main()

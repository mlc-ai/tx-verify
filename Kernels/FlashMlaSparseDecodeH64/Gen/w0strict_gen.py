#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Strict twins of the pure data sites of warpgroup 0.

Reads the generated tolerant files (`Proof/Wg0/Gen/{DataSites,DataSteps,EpiOut,EpiSites}*.lean`) and
writes `Strict<name>.lean` beside each: `reachS_<pc>` (`ReachS` for `Reach`, `reachS_frameSet` for
`reach_frameSet`) and `dsS_<pc>` (`DataStepE` for `DataStep`) for every site whose window has no value
run (`Gen.<run>_run`). The sites with value runs are the mixed windows and are not translated.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
GEN = ROOT / "Kernels/FlashMlaSparseDecodeH64/Proof/Wg0/Gen"
NS = "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0"
SRC = [
    "DataSites0",
    "DataSites1",
    "DataSites2",
    "DataSteps0",
    "DataSteps1",
    "EpiOut0",
    "EpiOut1",
    "EpiOut2",
    "EpiOut3",
    "EpiSites",
]
# explicit arguments of a kind before its `hwf` (after `P L g w`, with `e` counted), and the premise
HWF = {"ld1": (5, "EvRdOk"), "ld2": (6, "EvRdOk"), "nc": (8, "EvNcOk"), "ncv": (8, "EvNcOk")}
SKIP_STRICT_IMPORT = ()


def blocks(text):
    text = re.sub(r"\nend\nend PTX[\w.]*\s*$", "\n", text)
    return re.split(r"\n(?=/-- |theorem |def )", text)


def tokens(text, pos):
    """Balanced argument tokens of an application starting at `pos`."""
    out, n = [], len(text)
    pairs = {"(": ")", "⟨": "⟩", "[": "]"}
    while pos < n:
        while pos < n and text[pos] in " \n":
            pos += 1
        if pos >= n or text[pos] == ")" or text.startswith("fun ", pos):
            break
        start, depth = pos, 0
        while pos < n:
            c = text[pos]
            if c in pairs:
                depth += 1
            elif c in ")⟩]":
                depth -= 1
            elif c in " \n" and depth == 0:
                break
            pos += 1
        out.append((start, pos))
        if depth != 0:
            break
    return out


def kind_fix(body):
    m = re.search(r"@ds_(\w+) P L g w", body)
    kind = m.group(1)
    end = m.end()
    toks = tokens(body, end)
    ins = {0: " _"}  # `e` after `d`
    if kind in HWF:
        k, _ = HWF[kind]
        ins[k] = " hwf"
    out, last = [], 0
    for i, (s, e) in enumerate(toks):
        if i in ins:
            out.append(body[last:e] if False else body[last:s])
        out.append(body[last:last] if False else "")
        last = last
    # rebuild: insertion after token 0 (`_` for e) and before token k+1 (hwf)
    res, cur = [], 0
    for i, (s, e) in enumerate(toks):
        if i == 0:
            res.append(body[cur:e] + " _")
            cur = e
        if kind in HWF and i == HWF[kind][0]:
            res.append(body[cur:s] + "hwf ")
            cur = s
    res.append(body[cur:])
    body = "".join(res)
    return body.replace(f"@ds_{kind} P L g w", f"@dsS_{kind} P L g w", 1), kind


def pure_reach_names():
    pure, mixed = set(), set()
    for f in SRC:
        for b in blocks((GEN / f"{f}.lean").read_text()):
            m = re.search(r"theorem (reach_\w+)", b)
            if m:
                (mixed if "_run" in b else pure).add(m.group(1))
    return pure, mixed


def conv_reach(b):
    b = b.replace("theorem reach_", "theorem reachS_").replace("Reach kernel", "ReachS kernel")
    return b.replace("reach_frameSet", "reachS_frameSet")


def conv_ds(b):
    b = re.sub(
        r"theorem ds_(\w+) : ∀ d : D, d\.c\.site = (\(.*?\)) →\n    DataStep \(code P L g w\) \(dF L\) d := by",
        lambda m: (
            f"theorem dsS_{m.group(1)} : ∀ (d : D) (e : Event), d.c.site = {m.group(2)} →\n"
            "    @@HYP@@DataStepE (code P L g w) (dF L) d e := by"
        ),
        b,
    )
    b, kind = kind_fix(b)
    hyp = f"{HWF[kind][1]} e → " if kind in HWF else ""
    b = b.replace("@@HYP@@", hyp)
    b = re.sub(
        r"(rintro ⟨⟨.*?⟩, b, hist, ok⟩) ⟨⟩",
        lambda m: m.group(1) + " e ⟨⟩" + (" hwf" if kind in HWF else ""),
        b,
    )
    return re.sub(r"\breach_(\w+)", r"reachS_\1", b)


def wrap(text):
    out = []
    for line in text.split("\n"):
        while len(line) > 100:
            k = line.rfind(" ", 0, 98)
            ind = len(line) - len(line.lstrip()) + 2
            out.append(line[:k])
            line = " " * ind + line[k + 1 :]
        out.append(line)
    return "\n".join(out)


def header(src, text):
    lines = []
    for ln in text.split("\n"):
        if ln.startswith("public import "):
            mod = ln.split()[2]
            if any(mod.endswith(s) for s in SKIP_STRICT_IMPORT):
                continue
            mm = re.match(rf"{re.escape(NS)}\.Gen\.(\w+)$", mod)
            if mm and mm.group(1) in SRC:
                mod = f"{NS}.Gen.Strict{mm.group(1)}"
            lines.append(f"public import {mod}")
    base = [
        f"public import {NS}.Data.KindsS",
        f"public import {NS}.Data.OutStepS",
        "public import Lemmas.Flow.DataOverFor",
        "public import Lemmas.Flow.DataStepEKinds",
    ]
    imports = lines + [b for b in base if b not in lines]
    return (
        "-- SPDX-License-Identifier: Apache-2.0\n"
        "-- Generated by Kernels/FlashMlaSparseDecodeH64/Gen/w0strict_gen.py; do not edit.\n"
        "-- domain: valid-rows\nmodule\n\n"
        + "\n".join(imports)
        + "\n\n@[expose] public section\n\n"
        "namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data\n"
        "open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64\n\n"
        "noncomputable section\n\n"
        "variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m0 : Mem0}\n"
    )


def main():
    pure, mixed = pure_reach_names()
    for f in SRC:
        text = (GEN / f"{f}.lean").read_text()
        out = [header(f, text)]
        for b in blocks(text):
            if re.search(r"theorem reach_\w+", b) and "_run" not in b:
                out.append(conv_reach(b))
            elif re.search(r"theorem ds_\w+", b):
                rs = set(re.findall(r"\breach_\w+", b))
                if rs and rs <= pure:
                    out.append(conv_ds(b))
        out.append("end\nend PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data\n")
        (GEN / f"Strict{f}.lean").write_text(wrap("\n".join(x.rstrip("\n") + "\n" for x in out)))


if __name__ == "__main__":
    main()

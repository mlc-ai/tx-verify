# SPDX-License-Identifier: Apache-2.0
"""Write the chunked `decode_eq` of a frozen kernel PTX.

One kernel reduction of `Decode.kernelIn` over the whole program of several thousand instructions
does not fit in one file's time budget, so `decode_eq` is checked in parts that build in parallel
(`Kernels/<K>/Audit/Decode*.lean`): `DecodePrep` writes the result of `Decode.prepare` as closed
terms, `DecodeHeader` and `DecodeSource*` prove that `prepare` computes them, `DecodeCode*` prove
that consecutive slices of the instruction list decode to the matching slices of
`Decoded.kernel.code`, and `Decode` assembles `decode_eq` with the lemmas of
`Lemmas/Kernel/DecodeChunks.lean`. The instruction count is read from `code_length` in
`Data/Decoded.lean` and the kernel function's name from `Ptx.lean`.

    python Tools/decode_chunks.py --kernel FlashAttn4Fwd
    python Tools/decode_chunks.py --kernel FlashMlaSparseDecodeH64 --code-chunk 256 --no-heartbeats
    python Tools/decode_chunks.py --kernel TmlFa4Fwd

For TmlFa4Fwd the scope resolution of `prepare` is itself split into `DecodeScope*` files, which
`DecodeResolved` assembles into `prepare_eq`; `DecodeHeader` and `DecodeSource*` rewrite with it.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# Per-kernel display name and elaborator prefix.  A kernel not listed here uses its directory
# name and that name as the prefix.
DISPLAY = {
    "FlashAttn4Fwd": "FlashAttention-4 forward",
    "FlashMlaSparseDecodeH64": "FlashMLA sparse decode head64",
    "TmlFa4Fwd": "tml-fa4 SM100 forward",
}
ELAB = {"FlashAttn4Fwd": "fa4", "FlashMlaSparseDecodeH64": "flashmla", "TmlFa4Fwd": "tmlfa4"}
# Per-kernel defaults of `--code-chunk` and `--heartbeats`.
DEFAULTS = {"TmlFa4Fwd": (64, 0)}

# Instructions per `DecodeCode*` file and number of `DecodeSource*` files.
CODE_CHUNK = 289
SOURCE_PARTS = 4

HEAD = "-- SPDX-License-Identifier: Apache-2.0\nmodule\n\n"
REDUCE = (
    "-- The kernel unfolds `Nat.repr` in the scope-qualified names, so its body is imported.\n"
    "import all Init.Data.ToString.Extra\nimport all Init.Data.Repr\n"
)


class Layout:
    """Paths and names of one kernel's chunked decode audit."""

    def __init__(self, kernel, code_chunk, source_parts, heartbeats, header_literal=False):
        self.kernel = kernel
        self.kernel_dir = ROOT / "Kernels" / kernel
        self.out = self.kernel_dir / "Audit"
        self.mod = f"Kernels.{kernel}.Audit."
        self.ns = f"PTX.Kernels.{kernel}.DecodeAudit"
        self.gen = f"PTX.Generated.{kernel}"
        self.gen_short = f"Generated.{kernel}"
        self.display = DISPLAY.get(kernel, kernel)
        self.elab = ELAB.get(kernel, kernel)
        self.code_chunk = code_chunk
        self.source_parts = source_parts
        self.heartbeats = heartbeats
        self.header_literal = header_literal

    @property
    def common(self):
        return f"""public import {self.mod}DecodePrep
{REDUCE}
@[expose] public section

namespace {self.ns}

open PTX PTX.Decode

set_option maxRecDepth 100000
"""

    @property
    def heartbeat_option(self):
        if self.heartbeats == 0:
            return ""
        return (
            "-- The kernel reduction of `prepare` resolves every nested scope of the function.\n"
            f"set_option maxHeartbeats {self.heartbeats}\n"
        )

    def with_doc(self, doc):
        return self.common.replace("@[expose]", f"/-! {doc} -/\n\n@[expose]", 1)

    def total_instructions(self):
        text = (self.kernel_dir / "Data" / "Decoded.lean").read_text()
        m = re.search(r"theorem code_length : kernel\.code\.length = (\d+)", text)
        if m is None:
            sys.exit("Data/Decoded.lean has no `code_length` theorem")
        return int(m.group(1))

    def function_name(self):
        text = (self.kernel_dir / "Ptx.lean").read_text()
        names = re.findall(r"^def\s+(\S+)\s+: Function where", text, re.MULTILINE)
        if len(names) != 1:
            sys.exit(f"Ptx.lean defines {len(names)} kernel functions, expected 1")
        return names[0]

    @property
    def prep_doc(self):
        if self.kernel in ("FlashAttn4Fwd", "TmlFa4Fwd"):
            name = self.display.removesuffix(" forward")
            return (
                "The decoding environment and the scope-resolved instruction list of the "
                f"{name}\nforward kernel, as closed terms. `Decode.prepare` computes "
                "both from the whole function; its\nkernel reduction resolves every nested scope "
                "and costs tens of seconds, so the chunks of\n`decode_eq` decode against these "
                "terms instead. The terms are written by evaluating\n`Decode.prepare` at "
                "elaboration time, and `DecodeHeader` and `DecodeSource*` prove by kernel\n"
                "reduction that they are exactly what `Decode.prepare` computes, so the evaluation "
                "is not\ntrusted."
            )
        return (
            f"The decoding environment and the scope-resolved instruction list of the\n"
            f"{self.display} kernel, as closed terms. `Decode.prepare` computes both from the\n"
            f"whole function; its kernel reduction resolves every nested scope and costs tens of\n"
            f"seconds, so the chunks of `decode_eq` decode against these terms instead. The terms\n"
            f"are written by evaluating `Decode.prepare` at elaboration time, and `DecodeHeader`\n"
            f"and `DecodeSource*` prove by kernel reduction that they are exactly what\n"
            f"`Decode.prepare` computes, so the evaluation is not trusted."
        )

    def prep(self, name, size, source_starts):
        parts = "".join(
            f"""
set_option maxRecDepth 100000 in
/-- The instructions of `source` from index {a}, {size} of them. -/
def instrs{k} : List SourceInstr := {self.elab}_prepared_instrs% {a} {size}
"""
            for k, a in enumerate(source_starts)
        )
        n = len(source_starts)
        concat = " ++ (".join(f"instrs{k}" for k in range(n)) + ")" * (n - 1)
        return (
            HEAD
            + f"""public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.{self.kernel}.Ptx
public meta import Kernels.{self.kernel}.Ptx
public import Kernels.{self.kernel}.Data.Decoded
public import Lemmas.Kernel.DecodeChunks
public import Tactics.KernelRfl
public meta import Lean.ToExpr
public meta import Lean.Elab.Command

@[expose] public section

/-! {self.prep_doc} -/

namespace {self.ns}

open PTX PTX.Decode Lean

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

/-- The kernel function of the frozen module. -/
abbrev source : Syntax.Function :=
  {self.gen_short}.{name}

meta section
deriving instance ToExpr for PTX.Syntax.Operand
deriving instance ToExpr for PTX.Decode.RegClass
deriving instance ToExpr for PTX.ParamObjectDecl
deriving instance ToExpr for PTX.Decode.Env
end

/-- The environment (`none`) or the instructions from index `a`, `n` of them (`some (a, n)`),
that the compiled decoder computes for `source`, as a term. -/
meta def preparedTerm (slice : Option (Nat × Nat)) : Elab.Term.TermElabM Expr := do
  match prepare {self.gen_short}.module.globals
    {self.gen_short}.{name} with
  | .error e => throwError "Decode.prepare failed: {{e}}"
  | .ok p => return match slice with
    | none => toExpr p.env
    | some (a, n) => toExpr ((p.instrs.drop a).take n)

elab "{self.elab}_prepared_env%" : term => preparedTerm none
elab "{self.elab}_prepared_instrs%" a:num n:num : term => preparedTerm (some (a.getNat, n.getNat))

set_option maxRecDepth 100000 in
/-- The decoding environment of `source`. -/
def env : Env := {self.elab}_prepared_env%
{parts}
/-- The scope-resolved instructions of `source`, in source order. -/
def instrs : List SourceInstr := {concat}

end {self.ns}
"""
        )

    def header(self):
        doc = "`Decode.prepare` computes the environment `env` and the kernel header of\n"
        doc += "`Decoded.kernel`."
        rhs = (
            "(env, Decoded.metadata)"
            if self.header_literal
            else "(env, { Decoded.kernel with code := [] })"
        )
        if self.header_literal:
            stmt = (
                f"(prepare {self.gen_short}.module.globals source).map\n"
                f"    (fun p => (p.env, p.header)) = .ok {rhs}"
            )
        else:
            stmt = (
                f"(prepare {self.gen_short}.module.globals source).map\n"
                f"    (fun p => (p.env, p.header)) = .ok {rhs}"
            )
        return (
            HEAD
            + self.with_doc(doc)
            + f"""
{self.heartbeat_option}
theorem header_eq : {stmt} := by
  kernel_rfl

end {self.ns}
"""
        )

    def source_part(self, k, a, size, last):
        if last:
            lhs, rhs = f"p.instrs.drop {a}", f"instrs.drop {a}"
            what = f"from index {a} to the end"
        else:
            lhs, rhs = f"(p.instrs.drop {a}).take {size}", f"(instrs.drop {a}).take {size}"
            what = f"from index {a}, {size} of them"
        return (
            HEAD
            + self.with_doc(f"`Decode.prepare` computes the instructions of `instrs` {what}.")
            + f"""
{self.heartbeat_option}
theorem source_{k} : (prepare {self.gen_short}.module.globals source).map
    (fun p => {lhs}) = .ok ({rhs}) := by
  -- Stated against the closed part `instrs{k}`, the reduction compares only this slice.
  have h : {rhs} = instrs{k} := by kernel_rfl
  rw [h]
  kernel_rfl

end {self.ns}
"""
        )

    def code_part(self, k, a, last):
        if last:
            stmt = f"code env {a} (instrs.drop {a}) = .ok (Decoded.kernel.code.drop {a})"
            what = f"from index {a} to the end"
        else:
            stmt = (
                f"code env {a} ((instrs.drop {a}).take {self.code_chunk}) =\n"
                f"    .ok ((Decoded.kernel.code.drop {a}).take {self.code_chunk})"
            )
            what = f"from index {a}, {self.code_chunk} of them"
        doc = f"The instructions of `instrs` {what} decode to the same slice of\n"
        doc += "`Decoded.kernel.code`."
        return (
            HEAD
            + self.with_doc(doc)
            + f"""
theorem code_{k} : {stmt} := by
  kernel_rfl

end {self.ns}
"""
        )

    def assemble(self, name, total, source_starts, code_starts):
        imports = "".join(
            f"public import {self.mod}DecodeSource{k}\n" for k in range(len(source_starts))
        )
        imports += "".join(
            f"public import {self.mod}DecodeCode{k:02d}\n" for k in range(len(code_starts))
        )
        src_chain = f"source_{len(source_starts) - 1}"
        for k in reversed(range(len(source_starts) - 1)):
            src_chain = f"map_drop_chunk source_{k} ({src_chain})"
        code_chain = f"code_{len(code_starts) - 1}"
        for k in reversed(range(len(code_starts) - 1)):
            code_chain = f"code_chunk code_{k}\n      ({code_chain})"
        return (
            HEAD
            + f"""public import {self.mod}DecodeHeader
{imports}
@[expose] public section

/-! The frozen production PTX of the {self.display} kernel decodes to the exact
{total}-instruction program `Decoded.kernel`. The Core decoder `Decode.kernelIn` is checked by
kernel reduction in parts that build in parallel: `header_eq` and `source_*` for what
`Decode.prepare` computes, and `code_*` for consecutive slices of the instruction list;
`Lemmas/Kernel/DecodeChunks.lean` assembles them. -/

namespace PTX.Kernels.{self.kernel}

open PTX PTX.Decode DecodeAudit

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

theorem decode_eq : Decode.kernelIn {self.gen_short}.module.globals
    {self.gen_short}.{name} =
    .ok Decoded.kernel :=
  kernelIn_of_parts header_eq
    ({src_chain})
    ({code_chain})

end PTX.Kernels.{self.kernel}
"""
        )

    def render(self):
        """The generated files, by file name."""
        total, name = self.total_instructions(), self.function_name()
        code_starts = list(range(0, total, self.code_chunk))
        size = -(-total // self.source_parts)
        source_starts = list(range(0, total, size))
        files = {"DecodePrep": self.prep(name, size, source_starts), "DecodeHeader": self.header()}
        for k, a in enumerate(source_starts):
            last = k == len(source_starts) - 1
            files[f"DecodeSource{k}"] = self.source_part(k, a, size, last)
        for k, a in enumerate(code_starts):
            files[f"DecodeCode{k:02d}"] = self.code_part(k, a, k == len(code_starts) - 1)
        files["Decode"] = self.assemble(name, total, source_starts, code_starts)
        if self.kernel == "TmlFa4Fwd":
            files.update(scope_files(self.kernel_dir, name))
            for stem in ["DecodeHeader", *(f"DecodeSource{k}" for k in range(len(source_starts)))]:
                text = files[stem].replace(".Audit.DecodePrep", ".Audit.DecodeResolved")
                marker = "  kernel_rfl\n\nend"
                assert text.count(marker) == 1
                files[stem] = text.replace(marker, "  rw [prepare_eq]\n" + marker)
        return {f"{stem}.lean": text for stem, text in files.items()}


def scope_files(folder, name):
    """Certificate for resolving the exported top-level PTX body in separate files."""
    from export_lean import chunks
    from parse_ptx import parse

    (f,) = parse((folder / "full_p16_s1.ptx").read_text()).functions
    raw_parts = chunks(f.body)
    sizes = [len(part) for part in raw_parts]

    def depth(body):
        return max((depth(s.body) + 1 for s in body if s.kind == "scope"), default=1)

    fuel = depth(f.body) - 1
    generated = "Generated.TmlFa4Fwd"
    audit = "Kernels.TmlFa4Fwd.Audit."
    head = (
        HEAD
        + f"""public import {audit}DecodePrep
public import Lemmas.Kernel.DecodeScopes
public meta import Lean.ToExpr
public meta import Core.Source.Decode
public meta import Kernels.TmlFa4Fwd.Ptx
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax Lean

set_option linter.style.longLine false
set_option maxRecDepth 100000
"""
    )
    aliases = "\n".join(f"abbrev raw{k} := {generated}.{name}_body{k}" for k in range(len(sizes)))
    setup = (
        head
        + f"""
meta section
deriving instance ToExpr for PTX.Syntax.Statement
deriving instance ToExpr for PTX.Decode.Binding
end

{aliases}

elab "tml_scope_env%" : term => do
  match scopeBindings {generated}.{name}.body [] "" with
  | .ok bs => return toExpr bs
  | .error e => throwError "scope bindings: {{e}}"

def rootBindings : List Binding := tml_scope_env%

theorem rootBindings_eq : scopeBindings source.body [] "" = .ok rootBindings := by
  kernel_rfl

elab "tml_resolved_part%" start:num count:num : term => do
  let body := {generated}.{name}.body
  let fuel := scopeDepth body - 1
  let off := start.getNat
  let result := do
    let env ← scopeBindings body [] ""
    resolveScopePart (resolveScopes fuel) ((body.drop off).take count.getNat) env "" off
  match result with
  | .ok part => return toExpr part
  | .error e => throwError "scope resolution: {{e}}"

def rootFuel : Nat := {fuel}

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
"""
    )
    files = {"DecodeScopeSetup": setup}
    offset = 0
    starts = []
    for k, size in enumerate(sizes):
        starts.append(offset)
        files[f"DecodeScope{k:02d}"] = (
            HEAD
            + f"""public import {audit}DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved{k} : List Statement := tml_resolved_part% {offset} {size}

theorem resolved_{k} :
    resolveScopePart (resolveScopes rootFuel) raw{k} rootBindings "" {offset} =
      .ok resolved{k} := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
"""
        )
        offset += size

    def append_right(items):
        parts = list(items)
        return " ++ (".join(parts) + ")" * (len(parts) - 1)

    indices = range(len(sizes))
    joined = append_right(f"resolved{k}" for k in indices)
    tails = []
    for k in reversed(indices):
        raws = append_right(f"raw{i}" for i in indices[k:])
        parts = append_right(f"resolved{i}" for i in indices[k:])
        proof = f"resolved_{k}"
        if k < indices[-1]:
            proof = f"resolveScopePart_append resolved_{k} resolved_tail_{k + 1}"
        tails.append(f"""
private theorem resolved_tail_{k} :
    resolveScopePart (resolveScopes rootFuel) ({raws}) rootBindings "" {starts[k]} =
      .ok ({parts}) :=
  {proof}
""")
    imports = "".join(f"public import {audit}DecodeScope{k:02d}\n" for k in indices)
    raw_left = " ++ ".join(f"raw{k}" for k in indices)
    raw_right = append_right(f"raw{k}" for k in indices)
    depth_facts = "\n".join(
        f"private theorem depth_{k} : scopeDepth raw{k} = {depth(raw_parts[k])} := by kernel_rfl"
        for k in indices
    )
    depths = ", ".join(f"depth_{k}" for k in indices)
    files["DecodeResolved"] = (
        HEAD
        + imports
        + f"""
@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000
set_option Elab.async false

def resolved : List Statement :=
  {joined}

private theorem source_body_left : source.body = ({raw_left}) := rfl

private theorem source_body_right : source.body = ({raw_right}) := by
  simp only [source_body_left, List.append_assoc]

{depth_facts}

private theorem source_depth : scopeDepth source.body = rootFuel + 1 := by
  simp only [source_body_right, scopeDepth_append, {depths}]
  rfl
{"".join(tails)}
private theorem source_resolved :
    resolveScopes (scopeDepth source.body) source.body [] "" = .ok resolved := by
  apply resolveScopes_of_part source_depth rootBindings_eq
  have h := congrArg (fun body =>
    resolveScopePart (resolveScopes rootFuel) body rootBindings "" 0 = .ok resolved)
    source_body_right
  exact Eq.mpr h resolved_tail_0

theorem prepare_eq :
    prepare {generated}.module.globals source =
      prepareResolved {generated}.module.globals source resolved :=
  prepare_of_resolved (by kernel_rfl) (by kernel_rfl) source_resolved

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
"""
    )
    from lean_wrap import wrap_lines

    return {
        stem: "\n".join(wrap_lines(text.split("\n"))) if stem == "DecodeResolved" else text
        for stem, text in files.items()
    }


def main():
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    p.add_argument("--kernel", default="FlashAttn4Fwd", help="kernel directory name")
    p.add_argument("--code-chunk", type=int, default=None)
    p.add_argument("--source-parts", type=int, default=SOURCE_PARTS)
    p.add_argument(
        "--heartbeats",
        type=int,
        default=None,
        help="maxHeartbeats for the prepare reductions; 0 writes none",
    )
    p.add_argument("--no-heartbeats", action="store_true", help="same as --heartbeats 0")
    p.add_argument(
        "--header-literal",
        action="store_true",
        help="state header_eq against `Decoded.metadata`, which avoids unfolding "
        "`Decoded.kernel.code` in the reduction",
    )
    p.add_argument("--check", action="store_true", help="fail if a file is stale or missing")
    a = p.parse_args()
    code_chunk, heartbeats = DEFAULTS.get(a.kernel, (CODE_CHUNK, 1000000))
    layout = Layout(
        a.kernel,
        code_chunk if a.code_chunk is None else a.code_chunk,
        a.source_parts,
        0 if a.no_heartbeats else (heartbeats if a.heartbeats is None else a.heartbeats),
        a.header_literal,
    )
    files = layout.render()
    # Generated files that the current instruction count no longer produces.
    extra = sorted(
        f.name
        for f in layout.out.glob("Decode*.lean")
        if re.fullmatch(
            r"Decode(Prep|Header|Source\d+|Code\d+|ScopeSetup|Scope\d+|Resolved)?\.lean", f.name
        )
        and f.name not in files
    )
    if a.check:
        stale = [
            n
            for n, t in files.items()
            if not (layout.out / n).exists() or (layout.out / n).read_text() != t
        ]
        for n in stale + extra:
            print(f"stale: {layout.out / n}")
        return 1 if stale or extra else 0
    for n in extra:
        (layout.out / n).unlink()
    for n, t in files.items():
        (layout.out / n).write_text(t)
    return 0


if __name__ == "__main__":
    sys.exit(main())

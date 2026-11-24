-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.TmlFa4Fwd.Ptx
public meta import Kernels.TmlFa4Fwd.Ptx
public import Kernels.TmlFa4Fwd.Data.Decoded
public import Lemmas.Kernel.DecodeChunks
public import Tactics.KernelRfl
public meta import Lean.ToExpr
public meta import Lean.Elab.Command

@[expose] public section

/-! The decoding environment and the scope-resolved instruction list of the tml-fa4 SM100
forward kernel, as closed terms. `Decode.prepare` computes both from the whole function; its
kernel reduction resolves every nested scope and costs tens of seconds, so the chunks of
`decode_eq` decode against these terms instead. The terms are written by evaluating
`Decode.prepare` at elaboration time, and `DecodeHeader` and `DecodeSource*` prove by kernel
reduction that they are exactly what `Decode.prepare` computes, so the evaluation is not
trusted. -/

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode Lean

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

/-- The kernel function of the frozen module. -/
abbrev source : Syntax.Function :=
  Generated.TmlFa4Fwd.kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64div8_0

meta section
deriving instance ToExpr for PTX.Syntax.Operand
deriving instance ToExpr for PTX.Decode.RegClass
deriving instance ToExpr for PTX.ParamObjectDecl
deriving instance ToExpr for PTX.Decode.Env
end

/-- The environment (`none`) or the instructions from index `a`, `n` of them (`some (a, n)`),
that the compiled decoder computes for `source`, as a term. -/
meta def preparedTerm (slice : Option (Nat × Nat)) : Elab.Term.TermElabM Expr := do
  match prepare Generated.TmlFa4Fwd.module.globals
    Generated.TmlFa4Fwd.kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64div8_0 with
  | .error e => throwError "Decode.prepare failed: {e}"
  | .ok p => return match slice with
    | none => toExpr p.env
    | some (a, n) => toExpr ((p.instrs.drop a).take n)

elab "tmlfa4_prepared_env%" : term => preparedTerm none
elab "tmlfa4_prepared_instrs%" a:num n:num : term => preparedTerm (some (a.getNat, n.getNat))

set_option maxRecDepth 100000 in
/-- The decoding environment of `source`. -/
def env : Env := tmlfa4_prepared_env%

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 0, 2302 of them. -/
def instrs0 : List SourceInstr := tmlfa4_prepared_instrs% 0 2302

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 2302, 2302 of them. -/
def instrs1 : List SourceInstr := tmlfa4_prepared_instrs% 2302 2302

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 4604, 2302 of them. -/
def instrs2 : List SourceInstr := tmlfa4_prepared_instrs% 4604 2302

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 6906, 2302 of them. -/
def instrs3 : List SourceInstr := tmlfa4_prepared_instrs% 6906 2302

/-- The scope-resolved instructions of `source`, in source order. -/
def instrs : List SourceInstr := instrs0 ++ (instrs1 ++ (instrs2 ++ (instrs3)))

end PTX.Kernels.TmlFa4Fwd.DecodeAudit

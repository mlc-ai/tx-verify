-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.FlashAttn4Fwd.Ptx
public meta import Kernels.FlashAttn4Fwd.Ptx
public import Kernels.FlashAttn4Fwd.Data.Decoded
public import Lemmas.Kernel.DecodeChunks
public import Tactics.KernelRfl
public meta import Lean.ToExpr
public meta import Lean.Elab.Command

@[expose] public section

/-! The decoding environment and the scope-resolved instruction list of the FlashAttention-4
forward kernel, as closed terms. `Decode.prepare` computes both from the whole function; its
kernel reduction resolves every nested scope and costs tens of seconds, so the chunks of
`decode_eq` decode against these terms instead. The terms are written by evaluating
`Decode.prepare` at elaboration time, and `DecodeHeader` and `DecodeSource*` prove by kernel
reduction that they are exactly what `Decode.prepare` computes, so the evaluation is not
trusted. -/

namespace PTX.Kernels.FlashAttn4Fwd.DecodeAudit

open PTX PTX.Decode Lean

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

/-- The kernel function of the frozen module. -/
abbrev source : Syntax.Function :=
  Generated.FlashAttn4Fwd.kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tensor0000o11101213_tensor0000o11101213_tensor0000o10111213_tensor0000o11101213_None_None_None_Non_0

meta section
deriving instance ToExpr for PTX.Syntax.Operand
deriving instance ToExpr for PTX.Decode.RegClass
deriving instance ToExpr for PTX.ParamObjectDecl
deriving instance ToExpr for PTX.Decode.Env
end

/-- The environment (`none`) or the instructions from index `a`, `n` of them (`some (a, n)`),
that the compiled decoder computes for `source`, as a term. -/
meta def preparedTerm (slice : Option (Nat × Nat)) : Elab.Term.TermElabM Expr := do
  match prepare Generated.FlashAttn4Fwd.module.globals
    Generated.FlashAttn4Fwd.kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tensor0000o11101213_tensor0000o11101213_tensor0000o10111213_tensor0000o11101213_None_None_None_Non_0 with
  | .error e => throwError "Decode.prepare failed: {e}"
  | .ok p => return match slice with
    | none => toExpr p.env
    | some (a, n) => toExpr ((p.instrs.drop a).take n)

elab "fa4_prepared_env%" : term => preparedTerm none
elab "fa4_prepared_instrs%" a:num n:num : term => preparedTerm (some (a.getNat, n.getNat))

set_option maxRecDepth 100000 in
/-- The decoding environment of `source`. -/
def env : Env := fa4_prepared_env%

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 0, 1225 of them. -/
def instrs0 : List SourceInstr := fa4_prepared_instrs% 0 1225

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 1225, 1225 of them. -/
def instrs1 : List SourceInstr := fa4_prepared_instrs% 1225 1225

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 2450, 1225 of them. -/
def instrs2 : List SourceInstr := fa4_prepared_instrs% 2450 1225

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 3675, 1225 of them. -/
def instrs3 : List SourceInstr := fa4_prepared_instrs% 3675 1225

/-- The scope-resolved instructions of `source`, in source order. -/
def instrs : List SourceInstr := instrs0 ++ (instrs1 ++ (instrs2 ++ (instrs3)))

end PTX.Kernels.FlashAttn4Fwd.DecodeAudit

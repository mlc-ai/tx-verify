-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.FlashMlaSparseDecodeH64.Ptx
public meta import Kernels.FlashMlaSparseDecodeH64.Ptx
public import Kernels.FlashMlaSparseDecodeH64.Data.Decoded
public import Lemmas.Kernel.DecodeChunks
public import Tactics.KernelRfl
public meta import Lean.ToExpr
public meta import Lean.Elab.Command

@[expose] public section

/-! The decoding environment and the scope-resolved instruction list of the
FlashMLA sparse decode head64 kernel, as closed terms. `Decode.prepare` computes both from the
whole function; its kernel reduction resolves every nested scope and costs tens of
seconds, so the chunks of `decode_eq` decode against these terms instead. The terms
are written by evaluating `Decode.prepare` at elaboration time, and `DecodeHeader`
and `DecodeSource*` prove by kernel reduction that they are exactly what
`Decode.prepare` computes, so the evaluation is not trusted. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.DecodeAudit

open PTX PTX.Decode Lean

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

/-- The kernel function of the frozen module. -/
abbrev source : Syntax.Function :=
  Generated.FlashMlaSparseDecodeH64._ZN5sm1006decode6sparse6head6439flash_fwd_splitkv_mla_fp8_sparse_kernelINS2_14KernelTemplateIXtlNS2_6ConfigEL9ModelType0ELS6_0ELb0EEEEENS7_9TmaParamsIN4cute5tupleIJiiiiEEENS9_9TiledCopyINS9_9Copy_AtomIJNS9_11Copy_TraitsINS9_13SM90_TMA_LOADEJNS9_1CILi65536EEENS9_12AuxTmaParamsINSA_IJNS9_11ScaledBasisINSG_ILi1EEEJLi1EEEENSJ_ISK_JLi0EEEENSJ_ISK_JLi2EEEENSJ_ISK_JLi3EEEEEEERKNS9_6LayoutINSA_IJNSG_ILi64EEESR_SK_SK_EEESP_EERKNS9_7SwizzleILi3ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSQ_INSA_IJSK_NSA_IJNSA_IJNSA_IJSR_SR_EEENSG_ILi8EEEEEEEEEEEENSA_IJNSG_ILi0EEENSA_IJNSA_IJNSA_IJSR_SK_EEENSG_ILi4096EEEEEEEEEEEEEENSA_IJSR_NSG_ILi512EEEEEEEESB_NSC_INSD_IJNSE_INS9_14SM90_TMA_STOREEJSH_S10_EEES13_EEENSQ_INSA_IJSK_NSA_IJNSA_IJS15_SK_EEEEEEEEENSA_IJS1A_NSA_IJNSA_IJS1B_S1A_EEEEEEEEEEES15_EEEEEEv22SparseAttnDecodeParamsT0_

meta section
deriving instance ToExpr for PTX.Syntax.Operand
deriving instance ToExpr for PTX.Decode.RegClass
deriving instance ToExpr for PTX.ParamObjectDecl
deriving instance ToExpr for PTX.Decode.Env
end

/-- The environment (`none`) or the instructions from index `a`, `n` of them (`some (a, n)`),
that the compiled decoder computes for `source`, as a term. -/
meta def preparedTerm (slice : Option (Nat × Nat)) : Elab.Term.TermElabM Expr := do
  match prepare Generated.FlashMlaSparseDecodeH64.module.globals
    Generated.FlashMlaSparseDecodeH64._ZN5sm1006decode6sparse6head6439flash_fwd_splitkv_mla_fp8_sparse_kernelINS2_14KernelTemplateIXtlNS2_6ConfigEL9ModelType0ELS6_0ELb0EEEEENS7_9TmaParamsIN4cute5tupleIJiiiiEEENS9_9TiledCopyINS9_9Copy_AtomIJNS9_11Copy_TraitsINS9_13SM90_TMA_LOADEJNS9_1CILi65536EEENS9_12AuxTmaParamsINSA_IJNS9_11ScaledBasisINSG_ILi1EEEJLi1EEEENSJ_ISK_JLi0EEEENSJ_ISK_JLi2EEEENSJ_ISK_JLi3EEEEEEERKNS9_6LayoutINSA_IJNSG_ILi64EEESR_SK_SK_EEESP_EERKNS9_7SwizzleILi3ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSQ_INSA_IJSK_NSA_IJNSA_IJNSA_IJSR_SR_EEENSG_ILi8EEEEEEEEEEEENSA_IJNSG_ILi0EEENSA_IJNSA_IJNSA_IJSR_SK_EEENSG_ILi4096EEEEEEEEEEEEEENSA_IJSR_NSG_ILi512EEEEEEEESB_NSC_INSD_IJNSE_INS9_14SM90_TMA_STOREEJSH_S10_EEES13_EEENSQ_INSA_IJSK_NSA_IJNSA_IJS15_SK_EEEEEEEEENSA_IJS1A_NSA_IJNSA_IJS1B_S1A_EEEEEEEEEEES15_EEEEEEv22SparseAttnDecodeParamsT0_ with
  | .error e => throwError "Decode.prepare failed: {e}"
  | .ok p => return match slice with
    | none => toExpr p.env
    | some (a, n) => toExpr ((p.instrs.drop a).take n)

elab "flashmla_prepared_env%" : term => preparedTerm none
elab "flashmla_prepared_instrs%" a:num n:num : term => preparedTerm (some (a.getNat, n.getNat))

set_option maxRecDepth 100000 in
/-- The decoding environment of `source`. -/
def env : Env := flashmla_prepared_env%

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 0, 903 of them. -/
def instrs0 : List SourceInstr := flashmla_prepared_instrs% 0 903

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 903, 903 of them. -/
def instrs1 : List SourceInstr := flashmla_prepared_instrs% 903 903

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 1806, 903 of them. -/
def instrs2 : List SourceInstr := flashmla_prepared_instrs% 1806 903

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 2709, 903 of them. -/
def instrs3 : List SourceInstr := flashmla_prepared_instrs% 2709 903

/-- The scope-resolved instructions of `source`, in source order. -/
def instrs : List SourceInstr := instrs0 ++ (instrs1 ++ (instrs2 ++ (instrs3)))

end PTX.Kernels.FlashMlaSparseDecodeH64.DecodeAudit

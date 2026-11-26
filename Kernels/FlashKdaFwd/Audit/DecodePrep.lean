-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.FlashKdaFwd.Ptx
public meta import Kernels.FlashKdaFwd.Ptx
public import Kernels.FlashKdaFwd.Data.Decoded
public import Lemmas.Kernel.DecodeChunks
public import Tactics.KernelRfl
public meta import Lean.ToExpr
public meta import Lean.Elab.Command

@[expose] public section

/-! The decoding environment and the scope-resolved instruction list of the
FlashKdaFwd kernel, as closed terms. `Decode.prepare` computes both from the
whole function; its kernel reduction resolves every nested scope and costs tens of
seconds, so the chunks of `decode_eq` decode against these terms instead. The terms
are written by evaluating `Decode.prepare` at elaboration time, and `DecodeHeader`
and `DecodeSource*` prove by kernel reduction that they are exactly what
`Decode.prepare` computes, so the evaluation is not trusted. -/

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode Lean

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

/-- The kernel function of the frozen module. -/
abbrev source : Syntax.Function :=
  Generated.FlashKdaFwd._Z25_flash_kda_fwd_recurrenceIN4cute9TiledCopyINS0_9Copy_AtomIJNS0_11Copy_TraitsINS0_13SM90_TMA_LOADEJNS0_1CILi2048EEENS0_12AuxTmaParamsINS0_5tupleIJNS0_11ScaledBasisINS5_ILi1EEEJLi2EEEENS9_ISA_JLi1EEEENS9_IiJLi0EEEEEEERKNS0_6LayoutINS8_IJNS5_ILi8EEENS5_ILi16EEESA_EEENS8_IJSB_SC_NS9_ISA_JLi0EEEEEEEEERKNS0_7SwizzleILi0ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSF_INS8_IJSA_NS8_IJNS8_IJNS8_IJSG_SH_EEESH_EEEEEEEEENS8_IJNS5_ILi0EEENS8_IJNS8_IJNS8_IJSH_SA_EEENS5_ILi128EEEEEEEEEEEEEENS8_IJSA_SH_S13_EEEEENS1_INS2_IJNS3_IS4_JNS5_ILi512EEENS7_INS8_IJSJ_EEERKNSF_INS8_IJNS5_ILi32EEEEEES1B_EESR_EEEEESV_EEENSF_INS8_IJSA_NS8_IJNS8_IJS1C_SA_EEEEEEEEENS8_IJS11_NS8_IJNS8_IJSA_S11_EEEEEEEEEEES1D_EENS1_INS2_IJNS3_IS4_JS6_NS7_ISK_SN_SR_EEEEESV_EEES17_S18_EES1V_S1V_NS1_INS2_IJNS3_IS4_JNS5_ILi4096EEENS7_INS8_IJSC_SJ_EEERKNSF_INS8_IJS13_SA_EEES1X_EESR_EEEEEfEEENSF_INS8_IJSA_NS8_IJS1Y_EEEEEES1P_EENS8_IJSA_S13_EEEEENS1_IS1U_NSF_INS8_IJSA_NS8_IJNS8_IJSX_NS5_ILi2EEEEEEEEEEEES16_EENS8_IJSA_SH_SH_EEEEES2G_NS1_INS2_IJNS3_IS4_JNS5_ILi32768EEENS7_ISK_RKNSF_INS8_IJSG_S13_SA_EEESK_EERKNSO_ILi1ELi4ELi3EEEEEEEEfEEENSF_INS8_IJSA_NS8_IJNS8_IJNS8_IJSG_S13_EEESH_EEEEEEEEENS8_IJS11_NS8_IJNS8_IJS1Y_NS5_ILi1024EEEEEEEEEEEEEENS8_IJSA_S13_S13_EEEEENS1_INS2_IJNS3_INS0_14SM90_TMA_STOREEJS2H_S2P_EEEfEEES30_S31_EENS1_INS2_IJNS3_IS33_JS6_SS_EEESV_EEES17_S18_EELi16ELi128ELi3ELi2ELi192ELb1ELb1ELb1ELb1EEvT_T0_T1_T2_T3_T4_T5_T6_T7_T8_T9_PSV_iiiPKli

meta section
deriving instance ToExpr for PTX.Syntax.Operand
deriving instance ToExpr for PTX.Decode.RegClass
deriving instance ToExpr for PTX.ParamObjectDecl
deriving instance ToExpr for PTX.Decode.Env
end

/-- The environment (`none`) or the instructions from index `a`, `n` of them (`some (a, n)`),
that the compiled decoder computes for `source`, as a term. -/
meta def preparedTerm (slice : Option (Nat × Nat)) : Elab.Term.TermElabM Expr := do
  match prepare Generated.FlashKdaFwd.module.globals
    Generated.FlashKdaFwd._Z25_flash_kda_fwd_recurrenceIN4cute9TiledCopyINS0_9Copy_AtomIJNS0_11Copy_TraitsINS0_13SM90_TMA_LOADEJNS0_1CILi2048EEENS0_12AuxTmaParamsINS0_5tupleIJNS0_11ScaledBasisINS5_ILi1EEEJLi2EEEENS9_ISA_JLi1EEEENS9_IiJLi0EEEEEEERKNS0_6LayoutINS8_IJNS5_ILi8EEENS5_ILi16EEESA_EEENS8_IJSB_SC_NS9_ISA_JLi0EEEEEEEEERKNS0_7SwizzleILi0ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSF_INS8_IJSA_NS8_IJNS8_IJNS8_IJSG_SH_EEESH_EEEEEEEEENS8_IJNS5_ILi0EEENS8_IJNS8_IJNS8_IJSH_SA_EEENS5_ILi128EEEEEEEEEEEEEENS8_IJSA_SH_S13_EEEEENS1_INS2_IJNS3_IS4_JNS5_ILi512EEENS7_INS8_IJSJ_EEERKNSF_INS8_IJNS5_ILi32EEEEEES1B_EESR_EEEEESV_EEENSF_INS8_IJSA_NS8_IJNS8_IJS1C_SA_EEEEEEEEENS8_IJS11_NS8_IJNS8_IJSA_S11_EEEEEEEEEEES1D_EENS1_INS2_IJNS3_IS4_JS6_NS7_ISK_SN_SR_EEEEESV_EEES17_S18_EES1V_S1V_NS1_INS2_IJNS3_IS4_JNS5_ILi4096EEENS7_INS8_IJSC_SJ_EEERKNSF_INS8_IJS13_SA_EEES1X_EESR_EEEEEfEEENSF_INS8_IJSA_NS8_IJS1Y_EEEEEES1P_EENS8_IJSA_S13_EEEEENS1_IS1U_NSF_INS8_IJSA_NS8_IJNS8_IJSX_NS5_ILi2EEEEEEEEEEEES16_EENS8_IJSA_SH_SH_EEEEES2G_NS1_INS2_IJNS3_IS4_JNS5_ILi32768EEENS7_ISK_RKNSF_INS8_IJSG_S13_SA_EEESK_EERKNSO_ILi1ELi4ELi3EEEEEEEEfEEENSF_INS8_IJSA_NS8_IJNS8_IJNS8_IJSG_S13_EEESH_EEEEEEEEENS8_IJS11_NS8_IJNS8_IJS1Y_NS5_ILi1024EEEEEEEEEEEEEENS8_IJSA_S13_S13_EEEEENS1_INS2_IJNS3_INS0_14SM90_TMA_STOREEJS2H_S2P_EEEfEEES30_S31_EENS1_INS2_IJNS3_IS33_JS6_SS_EEESV_EEES17_S18_EELi16ELi128ELi3ELi2ELi192ELb1ELb1ELb1ELb1EEvT_T0_T1_T2_T3_T4_T5_T6_T7_T8_T9_PSV_iiiPKli with
  | .error e => throwError "Decode.prepare failed: {e}"
  | .ok p => return match slice with
    | none => toExpr p.env
    | some (a, n) => toExpr ((p.instrs.drop a).take n)

elab "FlashKdaFwd_prepared_env%" : term => preparedTerm none
elab "FlashKdaFwd_prepared_instrs%" a:num n:num : term => preparedTerm (some (a.getNat, n.getNat))

set_option maxRecDepth 100000 in
/-- The decoding environment of `source`. -/
def env : Env := FlashKdaFwd_prepared_env%

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 0, 959 of them. -/
def instrs0 : List SourceInstr := FlashKdaFwd_prepared_instrs% 0 959

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 959, 959 of them. -/
def instrs1 : List SourceInstr := FlashKdaFwd_prepared_instrs% 959 959

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 1918, 959 of them. -/
def instrs2 : List SourceInstr := FlashKdaFwd_prepared_instrs% 1918 959

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 2877, 959 of them. -/
def instrs3 : List SourceInstr := FlashKdaFwd_prepared_instrs% 2877 959

/-- The scope-resolved instructions of `source`, in source order. -/
def instrs : List SourceInstr := instrs0 ++ (instrs1 ++ (instrs2 ++ (instrs3)))

end PTX.Kernels.FlashKdaFwd.DecodeAudit

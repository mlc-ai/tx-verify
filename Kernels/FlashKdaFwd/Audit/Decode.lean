-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeHeader
public import Kernels.FlashKdaFwd.Audit.DecodeSource0
public import Kernels.FlashKdaFwd.Audit.DecodeSource1
public import Kernels.FlashKdaFwd.Audit.DecodeSource2
public import Kernels.FlashKdaFwd.Audit.DecodeSource3
public import Kernels.FlashKdaFwd.Audit.DecodeCode00
public import Kernels.FlashKdaFwd.Audit.DecodeCode01
public import Kernels.FlashKdaFwd.Audit.DecodeCode02
public import Kernels.FlashKdaFwd.Audit.DecodeCode03
public import Kernels.FlashKdaFwd.Audit.DecodeCode04
public import Kernels.FlashKdaFwd.Audit.DecodeCode05
public import Kernels.FlashKdaFwd.Audit.DecodeCode06
public import Kernels.FlashKdaFwd.Audit.DecodeCode07
public import Kernels.FlashKdaFwd.Audit.DecodeCode08
public import Kernels.FlashKdaFwd.Audit.DecodeCode09
public import Kernels.FlashKdaFwd.Audit.DecodeCode10
public import Kernels.FlashKdaFwd.Audit.DecodeCode11
public import Kernels.FlashKdaFwd.Audit.DecodeCode12
public import Kernels.FlashKdaFwd.Audit.DecodeCode13
public import Kernels.FlashKdaFwd.Audit.DecodeCode14

@[expose] public section

/-! The frozen production PTX of the FlashKdaFwd kernel decodes to the exact
3836-instruction program `Decoded.kernel`. The Core decoder `Decode.kernelIn` is checked by
kernel reduction in parts that build in parallel: `header_eq` and `source_*` for what
`Decode.prepare` computes, and `code_*` for consecutive slices of the instruction list;
`Lemmas/Kernel/DecodeChunks.lean` assembles them. -/

namespace PTX.Kernels.FlashKdaFwd

open PTX PTX.Decode DecodeAudit

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

theorem decode_eq : Decode.kernelIn Generated.FlashKdaFwd.module.globals
    Generated.FlashKdaFwd._Z25_flash_kda_fwd_recurrenceIN4cute9TiledCopyINS0_9Copy_AtomIJNS0_11Copy_TraitsINS0_13SM90_TMA_LOADEJNS0_1CILi2048EEENS0_12AuxTmaParamsINS0_5tupleIJNS0_11ScaledBasisINS5_ILi1EEEJLi2EEEENS9_ISA_JLi1EEEENS9_IiJLi0EEEEEEERKNS0_6LayoutINS8_IJNS5_ILi8EEENS5_ILi16EEESA_EEENS8_IJSB_SC_NS9_ISA_JLi0EEEEEEEEERKNS0_7SwizzleILi0ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSF_INS8_IJSA_NS8_IJNS8_IJNS8_IJSG_SH_EEESH_EEEEEEEEENS8_IJNS5_ILi0EEENS8_IJNS8_IJNS8_IJSH_SA_EEENS5_ILi128EEEEEEEEEEEEEENS8_IJSA_SH_S13_EEEEENS1_INS2_IJNS3_IS4_JNS5_ILi512EEENS7_INS8_IJSJ_EEERKNSF_INS8_IJNS5_ILi32EEEEEES1B_EESR_EEEEESV_EEENSF_INS8_IJSA_NS8_IJNS8_IJS1C_SA_EEEEEEEEENS8_IJS11_NS8_IJNS8_IJSA_S11_EEEEEEEEEEES1D_EENS1_INS2_IJNS3_IS4_JS6_NS7_ISK_SN_SR_EEEEESV_EEES17_S18_EES1V_S1V_NS1_INS2_IJNS3_IS4_JNS5_ILi4096EEENS7_INS8_IJSC_SJ_EEERKNSF_INS8_IJS13_SA_EEES1X_EESR_EEEEEfEEENSF_INS8_IJSA_NS8_IJS1Y_EEEEEES1P_EENS8_IJSA_S13_EEEEENS1_IS1U_NSF_INS8_IJSA_NS8_IJNS8_IJSX_NS5_ILi2EEEEEEEEEEEES16_EENS8_IJSA_SH_SH_EEEEES2G_NS1_INS2_IJNS3_IS4_JNS5_ILi32768EEENS7_ISK_RKNSF_INS8_IJSG_S13_SA_EEESK_EERKNSO_ILi1ELi4ELi3EEEEEEEEfEEENSF_INS8_IJSA_NS8_IJNS8_IJNS8_IJSG_S13_EEESH_EEEEEEEEENS8_IJS11_NS8_IJNS8_IJS1Y_NS5_ILi1024EEEEEEEEEEEEEENS8_IJSA_S13_S13_EEEEENS1_INS2_IJNS3_INS0_14SM90_TMA_STOREEJS2H_S2P_EEEfEEES30_S31_EENS1_INS2_IJNS3_IS33_JS6_SS_EEESV_EEES17_S18_EELi16ELi128ELi3ELi2ELi192ELb1ELb1ELb1ELb1EEvT_T0_T1_T2_T3_T4_T5_T6_T7_T8_T9_PSV_iiiPKli =
    .ok Decoded.kernel :=
  kernelIn_of_parts header_eq
    (map_drop_chunk source_0 (map_drop_chunk source_1 (map_drop_chunk source_2 (source_3))))
    (code_chunk code_0
      (code_chunk code_1
      (code_chunk code_2
      (code_chunk code_3
      (code_chunk code_4
      (code_chunk code_5
      (code_chunk code_6
      (code_chunk code_7
      (code_chunk code_8
      (code_chunk code_9
      (code_chunk code_10
      (code_chunk code_11
      (code_chunk code_12
      (code_chunk code_13
      (code_14)))))))))))))))

end PTX.Kernels.FlashKdaFwd

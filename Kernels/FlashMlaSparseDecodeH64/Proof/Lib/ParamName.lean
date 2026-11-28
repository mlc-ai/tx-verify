-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # The names of the two kernel parameters

The code names a parameter by its mangled symbol (`mov.b64 %rd2, <kernel>_param_0`); the Spec
names it `param i`. The two are the same string; the check reads `kernel.name` and compares the
two symbols character by character, once here. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- The symbol of parameter 0 is `param "0"`. -/
theorem param0_lit : param "0" =
      "_ZN5sm1006decode6sparse6head6439flash_fwd_splitkv_mla_fp8_sparse_kernelINS2_14Ke\
      rnelTemplateIXtlNS2_6ConfigEL9ModelType0ELS6_0ELb0EEEEENS7_9TmaParamsIN4cute5tupl\
      eIJiiiiEEENS9_9TiledCopyINS9_9Copy_AtomIJNS9_11Copy_TraitsINS9_13SM90_TMA_LOADEJN\
      S9_1CILi65536EEENS9_12AuxTmaParamsINSA_IJNS9_11ScaledBasisINSG_ILi1EEEJLi1EEEENSJ\
      _ISK_JLi0EEEENSJ_ISK_JLi2EEEENSJ_ISK_JLi3EEEEEEERKNS9_6LayoutINSA_IJNSG_ILi64EEES\
      R_SK_SK_EEESP_EERKNS9_7SwizzleILi3ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSQ_IN\
      SA_IJSK_NSA_IJNSA_IJNSA_IJSR_SR_EEENSG_ILi8EEEEEEEEEEEENSA_IJNSG_ILi0EEENSA_IJNSA\
      _IJNSA_IJSR_SK_EEENSG_ILi4096EEEEEEEEEEEEEENSA_IJSR_NSG_ILi512EEEEEEEESB_NSC_INSD\
      _IJNSE_INS9_14SM90_TMA_STOREEJSH_S10_EEES13_EEENSQ_INSA_IJSK_NSA_IJNSA_IJS15_SK_E\
      EEEEEEEENSA_IJS1A_NSA_IJNSA_IJS1B_S1A_EEEEEEEEEEES15_EEEEEEv22SparseAttnDecodePar\
      amsT0__param_0"
    := by decide +kernel

/-- The symbol of parameter 1 is `param "1"`. -/
theorem param1_lit : param "1" =
      "_ZN5sm1006decode6sparse6head6439flash_fwd_splitkv_mla_fp8_sparse_kernelINS2_14Ke\
      rnelTemplateIXtlNS2_6ConfigEL9ModelType0ELS6_0ELb0EEEEENS7_9TmaParamsIN4cute5tupl\
      eIJiiiiEEENS9_9TiledCopyINS9_9Copy_AtomIJNS9_11Copy_TraitsINS9_13SM90_TMA_LOADEJN\
      S9_1CILi65536EEENS9_12AuxTmaParamsINSA_IJNS9_11ScaledBasisINSG_ILi1EEEJLi1EEEENSJ\
      _ISK_JLi0EEEENSJ_ISK_JLi2EEEENSJ_ISK_JLi3EEEEEEERKNS9_6LayoutINSA_IJNSG_ILi64EEES\
      R_SK_SK_EEESP_EERKNS9_7SwizzleILi3ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSQ_IN\
      SA_IJSK_NSA_IJNSA_IJNSA_IJSR_SR_EEENSG_ILi8EEEEEEEEEEEENSA_IJNSG_ILi0EEENSA_IJNSA\
      _IJNSA_IJSR_SK_EEENSG_ILi4096EEEEEEEEEEEEEENSA_IJSR_NSG_ILi512EEEEEEEESB_NSC_INSD\
      _IJNSE_INS9_14SM90_TMA_STOREEJSH_S10_EEES13_EEENSQ_INSA_IJSK_NSA_IJNSA_IJS15_SK_E\
      EEEEEEEENSA_IJS1A_NSA_IJNSA_IJS1B_S1A_EEEEEEEEEEES15_EEEEEEv22SparseAttnDecodePar\
      amsT0__param_1"
    := by decide +kernel

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

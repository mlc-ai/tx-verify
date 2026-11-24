-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeHeader
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeSource0
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeSource1
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeSource2
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeSource3
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode00
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode01
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode02
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode03
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode04
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode05
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode06
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode07
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode08
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode09
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode10
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode11
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode12
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode13
public import Kernels.FlashMlaSparseDecodeH64.Audit.DecodeCode14

@[expose] public section

/-! The frozen production PTX of the FlashMLA sparse decode head64 kernel decodes to the exact
3612-instruction program `Decoded.kernel`. The Core decoder `Decode.kernelIn` is checked by
kernel reduction in parts that build in parallel: `header_eq` and `source_*` for what
`Decode.prepare` computes, and `code_*` for consecutive slices of the instruction list;
`Lemmas/Kernel/DecodeChunks.lean` assembles them. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64

open PTX PTX.Decode DecodeAudit

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

theorem decode_eq : Decode.kernelIn Generated.FlashMlaSparseDecodeH64.module.globals
    Generated.FlashMlaSparseDecodeH64._ZN5sm1006decode6sparse6head6439flash_fwd_splitkv_mla_fp8_sparse_kernelINS2_14KernelTemplateIXtlNS2_6ConfigEL9ModelType0ELS6_0ELb0EEEEENS7_9TmaParamsIN4cute5tupleIJiiiiEEENS9_9TiledCopyINS9_9Copy_AtomIJNS9_11Copy_TraitsINS9_13SM90_TMA_LOADEJNS9_1CILi65536EEENS9_12AuxTmaParamsINSA_IJNS9_11ScaledBasisINSG_ILi1EEEJLi1EEEENSJ_ISK_JLi0EEEENSJ_ISK_JLi2EEEENSJ_ISK_JLi3EEEEEEERKNS9_6LayoutINSA_IJNSG_ILi64EEESR_SK_SK_EEESP_EERKNS9_7SwizzleILi3ELi4ELi3EEEEEEEEN7cutlass10bfloat16_tEEEENSQ_INSA_IJSK_NSA_IJNSA_IJNSA_IJSR_SR_EEENSG_ILi8EEEEEEEEEEEENSA_IJNSG_ILi0EEENSA_IJNSA_IJNSA_IJSR_SK_EEENSG_ILi4096EEEEEEEEEEEEEENSA_IJSR_NSG_ILi512EEEEEEEESB_NSC_INSD_IJNSE_INS9_14SM90_TMA_STOREEJSH_S10_EEES13_EEENSQ_INSA_IJSK_NSA_IJNSA_IJS15_SK_EEEEEEEEENSA_IJS1A_NSA_IJNSA_IJS1B_S1A_EEEEEEEEEEES15_EEEEEEv22SparseAttnDecodeParamsT0_ =
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

end PTX.Kernels.FlashMlaSparseDecodeH64

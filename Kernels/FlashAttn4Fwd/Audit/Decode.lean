-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Audit.DecodeHeader
public import Kernels.FlashAttn4Fwd.Audit.DecodeSource0
public import Kernels.FlashAttn4Fwd.Audit.DecodeSource1
public import Kernels.FlashAttn4Fwd.Audit.DecodeSource2
public import Kernels.FlashAttn4Fwd.Audit.DecodeSource3
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode00
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode01
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode02
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode03
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode04
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode05
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode06
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode07
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode08
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode09
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode10
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode11
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode12
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode13
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode14
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode15
public import Kernels.FlashAttn4Fwd.Audit.DecodeCode16

@[expose] public section

/-! The frozen production PTX of the FlashAttention-4 forward kernel decodes to the exact
4897-instruction program `Decoded.kernel`. The Core decoder `Decode.kernelIn` is checked by
kernel reduction in parts that build in parallel: `header_eq` and `source_*` for what
`Decode.prepare` computes, and `code_*` for consecutive slices of the instruction list;
`Lemmas/Kernel/DecodeChunks.lean` assembles them. -/

namespace PTX.Kernels.FlashAttn4Fwd

open PTX PTX.Decode DecodeAudit

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

theorem decode_eq : Decode.kernelIn Generated.FlashAttn4Fwd.module.globals
    Generated.FlashAttn4Fwd.kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__tensor0000o11101213_tensor0000o11101213_tensor0000o10111213_tensor0000o11101213_None_None_None_Non_0 =
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
      (code_chunk code_14
      (code_chunk code_15
      (code_16)))))))))))))))))

end PTX.Kernels.FlashAttn4Fwd

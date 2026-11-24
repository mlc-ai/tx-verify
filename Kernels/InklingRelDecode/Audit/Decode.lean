-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Audit.DecodeHeader
public import Kernels.InklingRelDecode.Audit.DecodeSource0
public import Kernels.InklingRelDecode.Audit.DecodeSource1
public import Kernels.InklingRelDecode.Audit.DecodeSource2
public import Kernels.InklingRelDecode.Audit.DecodeSource3
public import Kernels.InklingRelDecode.Audit.DecodeCode00
public import Kernels.InklingRelDecode.Audit.DecodeCode01
public import Kernels.InklingRelDecode.Audit.DecodeCode02
public import Kernels.InklingRelDecode.Audit.DecodeCode03
public import Kernels.InklingRelDecode.Audit.DecodeCode04
public import Kernels.InklingRelDecode.Audit.DecodeCode05
public import Kernels.InklingRelDecode.Audit.DecodeCode06
public import Kernels.InklingRelDecode.Audit.DecodeCode07
public import Kernels.InklingRelDecode.Audit.DecodeCode08
public import Kernels.InklingRelDecode.Audit.DecodeCode09
public import Kernels.InklingRelDecode.Audit.DecodeCode10
public import Kernels.InklingRelDecode.Audit.DecodeCode11

@[expose] public section

/-! The frozen production PTX of the InklingRelDecode kernel decodes to the exact
2856-instruction program `Decoded.kernel`. The Core decoder `Decode.kernelIn` is checked by
kernel reduction in parts that build in parallel: `header_eq` and `source_*` for what
`Decode.prepare` computes, and `code_*` for consecutive slices of the instruction list;
`Lemmas/Kernel/DecodeChunks.lean` assembles them. -/

namespace PTX.Kernels.InklingRelDecode

open PTX PTX.Decode DecodeAudit

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

theorem decode_eq : Decode.kernelIn Generated.InklingRelDecode.module.globals
    Generated.InklingRelDecode._rel_verify_kernel =
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
      (code_11))))))))))))

end PTX.Kernels.InklingRelDecode

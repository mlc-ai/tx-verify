-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Core.Thread.Access

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit

/-- A length of one occupies bytes `01 00 00 00`. -/
theorem length_one_bytes :
    littleEndianBits (List.ofFn (fun k : Fin 4 => some (word32Byte 1 k))) = some 1 := rfl

/-- The signed masking sentinel occupies four bytes of `0xff`. -/
theorem invalid_index_bytes :
    littleEndianBits (List.ofFn (fun k : Fin 4 => some (word32Byte (i32Bits (-1)) k))) =
      some 0xffffffff := rfl

/-- A finite sink with nonzero high bytes retains its binary32 pattern. -/
theorem sink_one_bytes :
    littleEndianBits (List.ofFn (fun k : Fin 4 => some (word32Byte 0x3f800000 k))) =
      some 0x3f800000 := rfl

theorem sink_factor :
    f32Value 0x3FB8AA3B = some (12102203 / 8388608 : ℚ) := by
  norm_num [f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits,
    FloatFmt.expBits, FloatFmt.bias, FloatFmt.layout]

theorem lse_factor :
    f32Value 0x3F317218 = some (1453635 / 2097152 : ℚ) := by
  norm_num [f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits,
    FloatFmt.expBits, FloatFmt.bias, FloatFmt.layout]

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit

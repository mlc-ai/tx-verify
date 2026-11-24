-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TmemStore

/-! Decompressing `tcgen05.cp` (PROG-ISA-TC-CP, THREAD-TC-CP-DECOMPRESS, EXT-TCCP):
decoding, the destination bytes of 4-bit and 6-bit chunks, unknown source bytes, and the
rejected forms. -/
namespace PTX.Tests.TcCpDecompress
open PTX.TcCopy
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 2, 32⟩, ⟨"rd".toList, 1, 64⟩], labels := [], params := [] }

private def cp (q : String) : Except String Op :=
  Decode.op env q [.address [.register "r0"], .register "rd0"]

/-! ## Decoding -/

example : cp "tcgen05.cp.cta_group::1.128x256b.b8x16.b4x16_p64" =
    .ok (.tcCp .one .s128x256b 0 (.reg 2) (some .b4x16p64)) := rfl
example : cp "tcgen05.cp.cta_group::1.32x128b.warpx4.b8x16.b6x16_p32" =
    .ok (.tcCp .one .s32x128b 0 (.reg 2) (some .b6x16p32)) := rfl
-- Rejected: a destination format without a source format.
example : (cp "tcgen05.cp.cta_group::1.128x128b.b8x16").toOption = none := rfl
example : (Op.tcCp .one .s128x128b 0 (.reg 2) (some .b6x16p32)).rule = some .threadTc := rfl

/-! ## Destination bytes -/

-- 4-bit elements land in bits 5 to 2 (Figure 198): element 1 of `0x...F3` is 0xF, byte 0x3C.
example : decompressByte .b4x16p64 0xF3 0 = 0x0C := rfl
example : decompressByte .b4x16p64 0xF3 1 = 0x3C := rfl
-- The padding (elements past 15) never reaches a destination byte: byte 15 is bits 60 to 63.
example : decompressByte .b4x16p64 (2 ^ 64 + 0xA * 2 ^ 60) 15 = 0x28 := rfl
-- 6-bit elements land in bits 5 to 0 (Figures 200 and 201).
example : decompressByte .b6x16p32 0xFC1 0 = 0x01 := rfl
example : decompressByte .b6x16p32 0xFC1 1 = 0x3F := rfl
example : decompressByte .b6x16p32 (0x2A * 2 ^ 90) 15 = 0x2A := rfl

private def byte (n : Nat) : Option Byte := some (.bits 8 (BitVec.ofNat 64 n), 0)

-- One 16-byte row of 4-bit elements 0, 1, ..., 15 (bytes 0x10, 0x32, ...), then padding.
private def row4 : List (Option Byte) :=
  [0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE].map byte ++ List.replicate 8 (byte 0xFF)

-- Column 0 of the row holds elements 0 to 3, column 3 elements 12 to 15, each shifted by 2.
example : decompressedWord .b4x16p64 .s128x128b row4 0 0 =
    some (.bits 32 (BitVec.ofNat 64 (0x00 + 256 * 0x04 + 256 ^ 2 * 0x08 + 256 ^ 3 * 0x0C))) :=
  rfl
example : decompressedWord .b4x16p64 .s128x128b row4 0 3 =
    some (.bits 32 (BitVec.ofNat 64 (0x30 + 256 * 0x34 + 256 ^ 2 * 0x38 + 256 ^ 3 * 0x3C))) :=
  rfl
-- An unknown byte anywhere in the chunk, padding included, leaves every word of it unknown.
example : decompressedWord .b4x16p64 .s128x128b (row4.set 15 none) 0 0 = none := rfl
-- The copy without decompression keeps its bytes (the form before decompression).
example (c : Spec) (h : c.fmt = none) : cpWord c = word c.shape := cpWord_none h

end
end PTX.Tests.TcCpDecompress

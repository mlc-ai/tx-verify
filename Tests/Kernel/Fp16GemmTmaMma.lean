-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Support.TmaMma

/-! Production FP16 GEMM: concrete TMA box placements and MMA K-step descriptors. -/
namespace PTX.Tests.Fp16GemmTmaMma
open PTX.Kernels.Fp16Gemm8192

private def copyA : TensorCopy.Spec :=
  stageCopy (mapA 0 .small) (fun _ => 0) 0 1024 ⟨.shared, 0, 0⟩ true .two

-- Row 0 is unswizzled; row 1's first 16-byte chunk moves to the second chunk.
example : TensorCopy.writeLoc copyA 0 0 0 = some ⟨.shared, 0, 1024⟩ := rfl
example : TensorCopy.writeLoc copyA 63 0 1 = some ⟨.shared, 0, 1024 + 127⟩ := rfl
example : TensorCopy.writeLoc copyA 0 1 0 = some ⟨.shared, 0, 1024 + 144⟩ := rfl
example : TensorCopy.writeLoc copyA 8 1 0 = some ⟨.shared, 0, 1024 + 128⟩ := rfl
-- Outside the 64 x 128 box, or past an FP16 element's second byte, nothing is written.
example : TensorCopy.writeLoc copyA 64 0 0 = none := rfl
example : TensorCopy.writeLoc copyA 0 128 0 = none := rfl
example : TensorCopy.writeLoc copyA 0 0 2 = none := rfl

-- The production descriptors of K steps 0..3 for the stage at 1024.
example : TcShared.decode (4611756662049472512 + 64) = some (stepDescriptor 1024 0 0) := rfl
example : TcShared.decode (4611756662049472512 + 64 + 6) = some (stepDescriptor 1024 0 3) := rfl
-- K step 2 reads row 1, element 0 at the byte TMA wrote for element 32 of row 1.
example : TcShared.byteAddress 2 .k (stepDescriptor 1024 0 2) 1 0 0 =
    (TensorCopy.writeLoc copyA 32 1 0).map Loc.addr := rfl
example : TcShared.byteAddress 2 .k (stepDescriptor 1024 0 3) 127 15 1 =
    (TensorCopy.writeLoc copyA 63 127 1).map Loc.addr := rfl

-- The general statement, for any stage, step, row, index and byte.
example (s t y k byte : Nat) (hal : (16 * s) % 128 = 0) (hs : s + 2 * t < 32768)
    (ht : t < 4) (hy : y < 128) (hk : k < 16) (hb : byte < 2) :
    (TensorCopy.writeLoc (stageCopy (mapA 0 .large) (fun _ => 0) 1 (16 * s) ⟨.shared, 1, 8⟩
        true .two) (16 * t + k) y byte).map Loc.addr =
      (TcShared.decode (4611756662049472512 + s + 2 * t)).bind
        fun d => TcShared.byteAddress 2 .k d y k byte :=
  production_mma_reads_tma hal hs ht hy hk hb

end PTX.Tests.Fp16GemmTmaMma

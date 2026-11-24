-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaPremises

@[expose] public section

/-!
# The bytes of a Q store

The prologue packs the loaded query values into 32-bit words (`ProA.qWord dt i = joinValue
(dt.q (2 i)) (dt.q (2 i + 1))`) and writes each with one element of an `st.shared.v4.b32`
(`ProA.shape_stq`: element `w` of store `m` writes `storeValue 32 (qWord dt (4 m + w))` at
`qStoreBase + 4 w`). When the two loaded values are bf16 floats, the packed word is the pair of
the two (`qword_bytes`), and the four bytes the store writes are the two bytes of the lower value
then the two bytes of the upper (`qstore_value`): the byte-value half of `QTile.tile`. The address
half (the swizzled address `qAddr` of the tile element, i.e. the closed form of `qStoreBase`) and
the loaded values (`dt.q`) are rows of the thread-layer gap table.
`qstore_wbyte`: the byte a four-byte write covers at offset `p` is the `p`-th of its bytes.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- **Two bf16 values pack into their pair.** -/
theorem qword_bytes (x y : ℝ) :
    storeValue 32 (joinValue (.float .bf16 x) (.float .bf16 y)) =
      .ok (.pair (.float .bf16 x) (.float .bf16 y)) := by
  apply storeValue_of_bytes
  simp [joinValue, Value.bytes, FloatFmt.bytes]

/-- The bytes of a pair of bf16 values: the two bytes of the lower, then the two of the upper. -/
theorem pair_bytes (x y : ℝ) (z : Nat) (hz : z < 2) :
    (Value.pair (.float .bf16 x) (.float .bf16 y)).toBytes[z]? =
        some ((Value.float .bf16 x).byteAt z) ∧
      (Value.pair (.float .bf16 x) (.float .bf16 y)).toBytes[2 + z]? =
        some ((Value.float .bf16 y).byteAt z) := by
  constructor
  all_goals
    interval_cases z
    all_goals simp [Value.toBytes, Value.bytes, Value.byteAt, FloatFmt.bytes, List.range_succ]

/-- **The bytes of a Q store.** If the two query values packed into word `i` are the bf16 floats
`x` and `y`, the value the store writes has, at offsets `z` and `2 + z` (`z < 2`), byte `z` of `x`
and of `y`. -/
theorem qstore_value {dt : ProA.Dat} {i : Nat} {x y : ℝ} (hx : dt.q (2 * i) = .float .bf16 x)
    (hy : dt.q (2 * i + 1) = .float .bf16 y) {v : Value}
    (hv : storeValue 32 (ProA.qWord dt i) = .ok v) {z : Nat} (hz : z < 2) :
    v.toBytes[z]? = some ((Value.float .bf16 x).byteAt z) ∧
      v.toBytes[2 + z]? = some ((Value.float .bf16 y).byteAt z) := by
  unfold ProA.qWord at hv
  rw [hx, hy, qword_bytes] at hv
  have := Except.ok.inj hv
  rw [← this]
  exact pair_bytes x y z hz

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma

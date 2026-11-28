-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiLse
import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiRun
public import Kernels.InklingRelDecode.Proof.Lib.EpiWords

@[expose] public section

/-! # The LSE words the epilogue stores

The word of `lse_store` (the normalizer of the carried maximum and the sum, or the `-inf` pattern
for a zero sum) is the specification's `lseWord`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Proof PTX.Flow Lib.SoftRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem inf_bits : (FVal.inf true).toValue .f32 =
    .bits 32 (truncBits 32 (BitVec.ofInt 64 (-8388608))) := by
  decide

/-- **The LSE store of a row writes the bytes of `lseWord`.** -/
theorem lse_out_store (hX : Consistent L kernel Assumptions.all m X) (hsp : 0 < Q.splits)
    (hs : 0 < Q.scale) {z x tok h : Nat} {l mr : ℝ} (hl : 0 ≤ l) {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (entry2 : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → 0 < l →
      t.regs 1914 = some (.float .f32 mr) ∧
        t.regs 498 = some (.float .f32 (Q.scale * log2eF32)))
    (wait : EpiWait L X g b) (hlk : (kState Q z x tok h 0).l = l)
    (hmk : l ≠ 0 → mr = ((kState Q z x tok h 0).m).toReal)
    {k : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨2682, .wr a bs⟩) :
    bs = (if rowSum Q z x tok h = 0 then (FVal.inf true).toValue .f32
      else Value.float .f32 (lsePart Q z x tok h)).toBytes := by
  rw [lse_store hX hl entry entry2 wait he, ← Lib.epiLse_eq Q hsp hs z x tok h 0]
  unfold lseV Lib.epiLseWord
  rw [hlk, inf_bits]
  by_cases hz : l = 0
  · simp [hz]
  · simp [hz, hmk hz]

/-- **The LSE store of a launch without a block writes the `-inf` pattern.** -/
theorem lse_out_store_zero (hX : Consistent L kernel Assumptions.all m X) {v : Value} {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g b)
    (hz : okPred (setpE (.unord .eq) false v (.bits 32 (BitVec.ofNat 64 0))) = true)
    {k : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨2682, .wr a bs⟩) :
    bs = ((FVal.inf true).toValue .f32).toBytes := by
  rw [lse_store_zero hX entry wait hz he, inf_bits]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values

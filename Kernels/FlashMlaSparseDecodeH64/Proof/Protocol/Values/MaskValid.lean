-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MaskWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen

@[expose] public section

/-! # The validity read keeps warpgroup 0's trace valid

The read at pc 289 sets the mask word of the block in progress to a 32-bit word (`valid_read_word`).
No vote has happened in the block yet (`w0_boundSeen`), so the words of the block are early-valid
with the new mask word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)

include hp hX hFw hR hI hB hN in
/-- **The validity read's payload** (pc 289): a 32-bit word, from the lane's own events before
the read (no undefined behaviour elsewhere is assumed). -/
theorem w0_pay_mask {g k : Nat} {a : Acc} {bs : List (Option Byte)}
    (hal : LaneUbFree X g k) (he : X.get (g, k) = some ⟨289, .rd a bs⟩) (hw : warp L g < 4) :
    ∃ n < 2 ^ 32, rebuild 3 bs = .ok (.bits 32 (BitVec.ofNat 64 n)) := by
  have hat : MbarRow.Wg0At L g 289 := ⟨hw, by norm_num, by norm_num⟩
  obtain ⟨x, hx, hlt, -⟩ := valid_read_word hp hX hFw hR hI hB hN hal he hat
  have hr : rebuild 3 bs = .ok (.bits 32 x) := by
    cases hrb : rebuild 3 bs with
    | error f => simp [hrb, Except.toOption] at hx
    | ok v => simp [hrb] at hx; subst hx; rfl
  exact ⟨x.toNat, hlt, by rw [hr]; simp⟩

include hp hX hFw hR hI hB hN

/-- **The validity read keeps the trace valid** (pc 289). -/
theorem w0Valid_snoc_mask {g k : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨289, .rd a bs⟩) (hw : warp L g < 4)
    (h : W0Valid P.scale ((X.tr g).take k)) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  rw [trace_take_succ he]
  obtain ⟨hb, -, -⟩ := w0_boundSeen hp hX hFw hw he (fun f hf => by cases hf)
    (by show 103 ≤ 289; omega) h
  exact w0Core_mask hp.scalePos rfl rfl hb
    (w0_pay_mask hp hX hFw hR hI hB hN (noUbBefore_of_get hX he) he hw) h

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

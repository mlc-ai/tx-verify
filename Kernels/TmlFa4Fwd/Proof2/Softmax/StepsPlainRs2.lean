-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainRsRun

@[expose] public section

/-! # A plain round's numeric row sum

State the generated add tree's result as `rsPG`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A plain round's row sum** is the number `rsPG`. -/
theorem rsP_float (hp : Pre p L m) (v : V) :
    Gen.rsumPb_v7598 (rbV p v) = .float .f32 (rsPG p v) := by
  have k4 := (rsumPb_ok hp v).2
  obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp
    (by kernel_rfl : (kRun (kOf rbL4) [.base (.add2 8980 8978 8979),
      .base (.unpack 5807 5808 8980)]).isSome = true)
  have hs := (kRun_sound hK' k4 (by simp [kFns, XItem.FnOk])).2
  have e7 : K' 5807 = .s .fl ∧ K' 5808 = .s .fl := by
    have : (kRun (kOf rbL4) [.base (.add2 8980 8978 8979),
        .base (.unpack 5807 5808 8980)]).map (fun K => (K 5807, K 5808)) =
        some (.s .fl, .s .fl) := by kernel_rfl
    rw [hK'] at this
    simpa using this
  have h0 := hs 5807
  have h1 := hs 5808
  rw [e7.1] at h0
  rw [e7.2] at h1
  obtain ⟨-, x, hx⟩ := h0
  obtain ⟨-, y, hy⟩ := h1
  have hx' : Assumption.readEReal .f32 (Gen.rsumPb_v7597_0 (rbV p v)) = some (.ok (x : EReal)) := by
    rw [show Gen.rsumPb_v7597_0 (rbV p v) = xFinal (lookupD (Gen.rsumPb_facts4 (rbV p v)))
      [.base (.add2 8980 8978 8979), .base (.unpack 5807 5808 8980)] 5807 from rfl]
    exact hx
  have hy' : Assumption.readEReal .f32 (Gen.rsumPb_v7597_1 (rbV p v)) = some (.ok (y : EReal)) := by
    rw [show Gen.rsumPb_v7597_1 (rbV p v) = xFinal (lookupD (Gen.rsumPb_facts4 (rbV p v)))
      [.base (.add2 8980 8978 8979), .base (.unpack 5807 5808 8980)] 5808 from rfl]
    exact hy
  have e : Gen.rsumPb_v7598 (rbV p v) = .float .f32 (x + y) := by
    show okVal (.bits 32 0) (floatE (addI false) [_, _]) = _
    rw [addE_reads hx' hy' (addEReal_coe x y), erealValue_coe]
    rfl
  have : rsPG p v = x + y := by unfold rsPG; rw [e]; rfl
  rw [this, e]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasSumTreeRun
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs2
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round's sum tree -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

private theorem rsumBb_value (W : Nat → Value)
    (k4 : ∀ r, (kOf rsumBbK3 r).Has (lookupD (Gen.rsumBb_facts3 W) r)) :
    Gen.rsumBb_v6646 W = .float .f32 (valR (Gen.rsumBb_v6646 W)) := by
  obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp
    (by kernel_rfl : (kRun (kOf rsumBbK3) [.base (.add2 8686 8684 8685),
      .base (.unpack 5124 5125 8686)]).isSome = true)
  have hs := (kRun_sound hK' k4 (by simp [kFns, XItem.FnOk])).2
  have e7 : K' 5124 = .s .fl ∧ K' 5125 = .s .fl := by
    have : (kRun (kOf rsumBbK3) [.base (.add2 8686 8684 8685),
        .base (.unpack 5124 5125 8686)]).map (fun K => (K 5124, K 5125)) =
        some (.s .fl, .s .fl) := by kernel_rfl
    rw [hK'] at this
    simpa using this
  have h0 := hs 5124
  have h1 := hs 5125
  rw [e7.1] at h0
  rw [e7.2] at h1
  obtain ⟨-, x, hx⟩ := h0
  obtain ⟨-, y, hy⟩ := h1
  have hx' : Assumption.readEReal .f32 (Gen.rsumBb_v6645_0 W) = some (.ok (x : EReal)) := by
    rw [show Gen.rsumBb_v6645_0 W = xFinal (lookupD (Gen.rsumBb_facts3 W))
      [.base (.add2 8686 8684 8685), .base (.unpack 5124 5125 8686)] 5124 from rfl]
    exact hx
  have hy' : Assumption.readEReal .f32 (Gen.rsumBb_v6645_1 W) = some (.ok (y : EReal)) := by
    rw [show Gen.rsumBb_v6645_1 W = xFinal (lookupD (Gen.rsumBb_facts3 W))
      [.base (.add2 8686 8684 8685), .base (.unpack 5124 5125 8686)] 5125 from rfl]
    exact hy
  have e : Gen.rsumBb_v6646 W = .float .f32 (x + y) := by
    show okVal (.bits 32 0) (floatE (addI false) [_, _]) = _
    rw [addE_reads hx' hy' (addEReal_coe x y), erealValue_coe]
    rfl
  rw [e]
  rfl

/-- **A bias round's row sum** is the number `rsB`. -/
theorem rsB_float (hp : Pre p L m) (v : V) :
    Gen.rsumBb_v6646 (rsumBbStart p L g v) = .float .f32 (rsB p L g v) :=
  rsumBb_value _ (rsumBb_ok (g := g) hp v).2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

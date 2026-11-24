-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Handoff
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.TmaWait
import Kernels.TmlFa4Fwd.Proof.Protocol.Ld.TmaBlk
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasPoll
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's Bias groups are the softmax lanes' bias polls

`bias_polled`: a tensor copy of group `u` of a Bias stage (after `u + 1` polls of the empty barrier)
is polled for by every lane of the stage that exits: the lane has made more than `u` polls of the
full barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The loader's Bias groups are polled for by every lane that exits.** -/
theorem bias_polled (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {st : Fin 2} {z i pc a u : Nat} {sp : TensorCopy.Spec}
    (he : X.get (z, i) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = bF L g st)
    (hu : ((X.tr z).take i).countP (issuesTo (bF L g st)) / 2 = u)
    {h k pcx : Nat} (hh : SoftIn L g st.val h) (hx : X.get (h, k) = some ⟨pcx, .exit⟩) :
    u < okPolls (bF L g st) ((X.tr h).take k) := by
  have hst := st.isLt
  obtain ⟨hzc, hzw⟩ := ld_copy_lane hp hX hFw (b_tmaOff st) he hm
  have hoff : bF L g st = obj L z (Loader.fOff (decide (st.val = 1))) := by
    rw [obj_cta hzc]
    have : Loader.fOff (decide (st.val = 1)) = 320 + 8 * st.val := by
      by_cases h1 : st.val = 1
      · simp [Loader.fOff, h1]
      · simp [Loader.fOff, h1]; omega
    rw [this]
  have hm' := hm
  rw [hoff] at hm'
  obtain ⟨R, bal, hP, hle⟩ := bias_copy_le hp hX hFw hzw he hm'
  have hcp := (ld_copy_polls hp hX hFw hzw (o := Loader.fOff (decide (st.val = 1)))
    (by unfold LdTmaOff; by_cases h1 : st.val = 1 <;> simp [Loader.fOff, h1]) he hm')
  rw [← hoff] at hcp
  have hPh := Epilogue.Picked.cta (hzc.trans hh.2.1.symm) hP
  have hrounds := Loader.biasPick_rounds (p := p) (L := L) (y := z) (g := h)
    (hzc.trans hh.2.1.symm) R bal
  have hstg : Softmax.stg L h = decide (st.val = 1) := by
    have key : ∀ w < 8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4 ≤ w) := by decide
    have hk : Softmax.stg L h = decide (4 ≤ Prologue.warpIndex L h) :=
      key (Prologue.warpIndex L h) hh.2.2.1
    rw [hk]
    have := hh.2.2.2
    by_cases h1 : st.val = 1
    · simp only [h1, decide_true, decide_eq_true_eq]; omega
    · simp only [h1, decide_false, decide_eq_false_iff_not]; omega
  rw [hstg] at hrounds
  have hB : StageRounds p L h (Softmax.nB p L h (softRef p L h R bal)).toNat := ⟨R, bal, hPh, rfl⟩
  have hex := soft_exit_bias hp hX hFw hh.2.2.1 hB hx
  have hsob : sobj L h 320 = bF L g st := by
    rw [sobj, obj_cta hh.2.1, hh.2.2.2, Nat.add_comm]
  rw [hsob] at hex
  generalize (Softmax.nB p L h (softRef p L h R bal)).toNat = B at hex hrounds
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof

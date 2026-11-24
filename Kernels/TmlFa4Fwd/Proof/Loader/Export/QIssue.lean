-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Lemmas.Flow.NotTensor
import Kernels.TmlFa4Fwd.Proof.Loader.Export.QGroup
import Kernels.TmlFa4Fwd.Proof.Loader.Export.TimeLag
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Loader.Export.QTx
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite

@[expose] public section

/-! # The loader's tensor copies on the Q stages -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.Flow (issuesTo)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The TMA group that completes on a Q stage. -/
theorem q_grp {o : Nat} (ho : o = 0 ∨ o = 8) :
    ∃ t : Fin 7, (t = 0 ∨ t = 2) ∧ Loader.taOff t = o := by
  rcases ho with rfl | rfl
  · exact ⟨0, .inl rfl, rfl⟩
  · exact ⟨2, .inr rfl, rfl⟩

/-- **A copy of a loader lane that completes on a Q stage** is a lane of warp 14's, after it won an
election, and the lane has issued at most one such copy before. -/
theorem q_issue (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : o = 0 ∨ o = 8) {h k pc a : Nat} {sp : TensorCopy.Spec}
    (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (he : X.get (h, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = obj L h o) :
    Prologue.warpIndex L h = 14 ∧
      (∃ j pc' mk inst, X.get (h, j) = some ⟨pc', .elect mk inst (laneOf L h)⟩) ∧
      ((X.tr h).take k).countP (issuesTo (obj L h o)) ≤ 1 := by
  have hmb : MbarOf ⟨pc, .tensorIssue a sp⟩ (obj L h o) := hm
  rcases LdWarp.open_ev hp hX hFw hw he (fun _ h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨b, d, n, hσ, hub, hR, -, hev⟩
  · exact absurd (start_mbar hev hi.2 hmb) (fun ⟨c, hc⟩ => by cases hc)
  have hJl := (hR.2 hub).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, -⟩ := hJl.refE
  cases ld_use hp hRing hev hmb with
  | slot _ _ _ _ _ hk | tw _ _ _ _ hk | dw _ _ _ _ hk | dq _ _ _ hk | arrive _ _ _ _ hk
  | ta _ _ _ _ hk | da _ _ _ hk => cases hk
  | tc t c a' s' hs hloc hk hb' =>
    have hw14 : Prologue.warpIndex L h = 14 := by
      rw [← hR.1]; exact hRing.tma (by rw [hs]; rfl)
    have hht := Frame.lt_of_get hX he
    obtain ⟨j, -, pc', mk, inst, hel⟩ := Loader.tc_won hp hX hht hw14 hσ hub hs
    refine ⟨hw14, ⟨j, pc', mk, inst, hel⟩, ?_⟩
    obtain ⟨t', ht', rfl⟩ := q_grp ho
    obtain rfl := Loader.q_group ht' (obj_off hloc).2.symm
    have := Loader.q_copies hp hX hht hw14 ht' hσ hub
    refine this.trans ?_
    rw [hs]
    have hc2 := c.isLt
    rcases ht' with rfl | rfl <;>
      simp only [Loader.ppos, Loader.cpos, Fin.val_zero, Fin.val_two, Nat.reduceLT,
        ↓reduceIte] <;> split_ifs <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader

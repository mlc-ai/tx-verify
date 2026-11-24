-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpStageProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpDecisionProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleRound
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotAgreement
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.CountTake
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Thread

/-- Each warp takes one common ballot branch. Its lanes reach the credit
instructions after exactly the tensor operations selected by that branch. -/
theorem rescaleWarpSignalOfBallotLanes {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g rank ord : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (stage : Fin 2) (F : Nat → List (Nat × Value))
    (f : ∀ h, SameWarp l g h → RescaleVisitFrame l h stage (F h))
    (c : ∀ h, SameWarp l g h → RescaleBallotLane l X h stage ord)
    (input : ∀ h (hs : SameWarp l g h), (c h hs).frame = F h ∧
      ((X.tr h).take (c h hs).cursor.pos).countP isTcColl = rank) :
    ∃ word : BitVec 32, ∀ h (hs : SameWarp l g h),
      let a := c h hs
      ∃ d : OpeningTripCursor l X h (rescaleSignalPc stage) (F h),
        X.get (h,a.cursor.pos) = some ⟨statsPc stage .alpha+2,
          .vote (2^32-1) (decide (a.alpha < 1)) word⟩ ∧
        d.pos = a.cursor.pos+1+rescaleBodyEvents word ∧
        ((X.tr h).take d.pos).countP isTcColl = rank+rescaleBodyEvents word := by
  classical
  have self : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  have each (h : Nat) (hs : SameWarp l g h) :=
    rescaleDecisionOfMaximal hp hMax hs.1.2.1 stage (fun k hk => c k (Step.sameWarp_trans hs hk))
  choose word voted mask cur pos using each
  have yes (h : Nat) (hs : SameWarp l g h) : word g self = word h hs := by
    have ballot {t : Nat} (u : SameWarp l g t) :
        CorrectionRescaleBallot X (t,(c t u).cursor.pos) (word t u) :=
      CorrectionRescaleBallot.ofEvent (by fin_cases stage <;> decide) (voted t u)
    obtain ⟨-,hk⟩ := (hFrame X hMax.1).metadataProtected hp
    exact CorrectionRescaleBallot.wordsAgree hp hMax.1 hs hw.1 hw.2 hk
      (ballot self) (ballot hs) (mask g self) (mask h hs)
  have count (h : Nat) (hs : SameWarp l g h) :
      ((X.tr h).take (cur h hs).pos).countP isTcColl = rank := by
    rw [pos,countP_take_succ_false (voted h hs) rfl]
    exact (input h hs).2
  have stripped (h : Nat) (hs : SameWarp l g h) :=
    (cur h hs).checkpoint.mono (cur h hs).checkpoint.2.2.2.2.2
  refine ⟨word g self,?_⟩
  by_cases zero : word g self = 0
  · intro h hs
    have z := (yes h hs).symm.trans zero
    let u := cur h hs
    have ht := stripped h hs
    have site : rescaleSkipPc stage = rescaleSignalPc stage := by fin_cases stage <;> rfl
    exact ⟨⟨u.pos,u.before,u.ready,u.ending,u.positive,u.bounded,u.released,
      ⟨(ht.1.trans (ite_eq_left z)).trans site,ht.2.1,ht.2.2.1,ht.2.2.2.1,
        by rw [← (input h hs).1]; exact ht.2.2.2.2⟩,u.recorded,u.remaining,u.localSteps⟩,
      (yes h hs).symm ▸ voted h hs,by simpa [rescaleBodyEvents,zero] using pos h hs,
      by simpa [rescaleBodyEvents,zero] using count h hs⟩
  · let coeff h := if hs : SameWarp l g h then (c h hs).coefficient else b32 0
    let alpha h := if hs : SameWarp l g h then (c h hs).alpha else 0
    let start (h : Nat) (hs : SameWarp l g h) : OpeningTripCursor l X h
        (rescaleLoadPc stage 0) (F h) :=
      let u := cur h hs
      ⟨u.pos,u.before,u.ready,u.ending,u.positive,u.bounded,u.released,by
        have ht := stripped h hs
        exact ⟨ht.1.trans (ite_eq_right ((yes h hs) ▸ zero)),ht.2.1,ht.2.2.1,ht.2.2.2.1,
          by rw [← (input h hs).1]; exact ht.2.2.2.2⟩,
        u.recorded,u.remaining,u.localSteps⟩
    have all := rescaleWarpProductsOfMaximal hp hMax hFrame stage F coeff alpha f start
      (fun h hs => ⟨count h hs,by simpa only [coeff,alpha,dite_eq_left hs] using (c h hs).valid,
        by simpa only [coeff,dite_eq_left hs] using (cur h hs).checkpoint.2.2.2.2.1⟩)
    intro h hs
    obtain ⟨d,hp',ht⟩ := all h hs
    refine ⟨d,(yes h hs).symm ▸ voted h hs,?_,?_⟩
    · simp only [rescaleBodyEvents,ite_eq_right zero,hp']
      exact congrArg (·+25) (pos h hs)
    · simpa only [rescaleBodyEvents,ite_eq_right zero] using ht

end PTX.Kernels.TmlFa4Fwd.Correction

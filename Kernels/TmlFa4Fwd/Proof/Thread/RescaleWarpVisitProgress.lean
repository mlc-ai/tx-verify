-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpBranchReturn
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleRoundReadProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleSignalProgress
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleVisitOrdinals
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue

/-- All lanes of a released correction rendezvous reach the end of this
stage, with their next tensor, ballot and named-barrier ordinals available. -/
theorem rescaleWarpVisitOfRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g rank ord : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (stage : Fin 2) (F : Nat → List (Nat × Value))
    (f : ∀ h, SameWarp l g h → RescaleVisitFrame l h stage (F h))
    (c : ∀ h, SameWarp l g h → RescaleWaitReached l X h stage (F h))
    (input : ∀ h (hs : SameWarp l g h),
      ((X.tr h).take (c h hs).index).countP isTcColl = rank ∧
      ((X.tr h).take (c h hs).index).countP isFullWarpVote = ord)
    (release : ∀ h (hs : SameWarp l g h), (c h hs).index+1 = (X.tr h).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Y.MemWrites = X.MemWrites ∧ Step.Released l Y h) :
    ∃ n, (n = 0 ∨ n = 25) ∧ ∀ h (hs : SameWarp l g h),
      ∃ d : OpeningTripCursor l X h (rescaleSignalPc stage+3) (F h),
        X.Arrive (h,d.pos-2) (creditLoc l h stage) 0 1 true .cta ∧
        X.Arrive (h,d.pos-1) (rescaleReuseLoc l h stage) 0 1 true .cta ∧
        ((X.tr h).take d.pos).countP isTcColl = rank+n ∧
        ((X.tr h).take d.pos).countP isFullWarpVote = ord+1 ∧
        ∀ id, ((X.tr h).take d.pos).countP (Execution.isBarId id) =
          ((X.tr h).take (c h hs).index).countP (Execution.isBarId id) +
            (if id = statsBarrierId l h stage then 1 else 0) := by
  classical
  have each (h : Nat) (hs : SameWarp l g h) :=
    (c h hs).ballotLane hp hMax hFrame hs.1.2.1 (f h hs) (release h hs)
  choose raw frame pos tensor bytes reads using each
  let lanes (h : Nat) (hs : SameWarp l g h) : RescaleBallotLane l X h stage ord :=
    let a := raw h hs
    ⟨a.frame,a.coefficient,a.alpha,a.valid,a.cursor,a.vote.trans (input h hs).2,a.fresh⟩
  obtain ⟨word,run⟩ := rescaleWarpSignalOfBallotLanes hp hMax hFrame hg hw stage F f lanes
    (fun h hs => ⟨frame h hs,(tensor h hs).trans (input h hs).1⟩)
  refine ⟨rescaleBodyEvents word,?_,?_⟩
  · unfold rescaleBodyEvents
    split
    · exact .inl rfl
    · exact .inr rfl
  intro h hs
  obtain ⟨s,hv,hPos,ht⟩ := run h hs
  obtain ⟨hA,hR,d,hd⟩ := rescaleSignalsOfMaximal hp hMax hs.1.2.1 stage s
    (f h hs).credit (f h hs).reuse (f h hs).release
  have balPos : (lanes h hs).cursor.pos = (c h hs).index+2 := pos h hs
  have tRank : ((X.tr h).take ((lanes h hs).cursor.pos+1)).countP isTcColl = rank := by
    rw [countP_take_succ_false hv rfl]
    exact (tensor h hs).trans (input h hs).1
  obtain ⟨tc,vote,bar⟩ := rescaleVisitCounts (c h hs).joined (reads h hs) hv hA hR
    balPos hPos hd (ht.trans (by rw [tRank]))
  have pa : d.pos-2 = s.pos := by omega
  have pr : d.pos-1 = s.pos+1 := by omega
  exact ⟨d,pa.symm ▸ hA,pr.symm ▸ hR,tc.trans (congrArg (·+_) (input h hs).1),
    vote.trans (congrArg (·+1) (input h hs).2),bar⟩

end PTX.Kernels.TmlFa4Fwd.Correction

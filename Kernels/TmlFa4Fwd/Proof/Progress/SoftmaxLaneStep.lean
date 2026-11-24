-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.SoftmaxPendingReadiness
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedStageVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxPlainStageVisit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread Softmax

/-- A softmax lane at the head of repeated visit `visit` of a loop with `trips` visits, of
which the last `split` are plain. The biased loop counter starts at `2^32-(trips-split)` and
the plain counter at `2^32-split`; the Tensor Memory count of a plain head adds 14 for every
earlier plain visit to the 11 of each earlier visit. -/
def LoopHeadAt (p : Params) (l : Launch) (X : Execution) (trips split g : Nat) (warp : Fin 8)
    (visit bars elects pos : Nat) : Prop :=
  (visit < trips-split ∧ ∃ block floor counter : Nat, ∃ maximum : Option ℝ, ∃ sum : ℝ,
    counter = 2^32-(trips-split)+(visit-1) ∧
    ∃ h : BiasedLoopHead p l X g warp visit block floor counter bars elects maximum sum,
      h.cursor.pos = pos ∧ h.split = split) ∨
  (trips-split ≤ visit ∧ ∃ counter tc : Nat, ∃ maximum : Option ℝ, ∃ sum : ℝ,
    counter = 2^32-split+(visit-(trips-split)) ∧
    tc = 11*(trips-split)+14*(visit-(trips-split)) ∧
    ∃ h : PlainLoopAt p l X g warp 6661 visit counter tc bars elects maximum sum,
      h.cursor.pos = pos)

/-- What a lane reaches after the correction credit of visit `visit`: the head of the next
visit, or the terminal statistics after the last visit. -/
def LoopNextAt (p : Params) (l : Launch) (X : Execution) (trips split g : Nat) (warp : Fin 8)
    (visit bars elects pos : Nat) : Prop :=
  (visit+1 < trips → LoopHeadAt p l X trips split g warp (visit+1) (bars+1) (elects+1) pos) ∧
    (visit+1 = trips → ∃ maximum sum, Nonempty (SoftmaxTerminalAt p l X g warp trips maximum sum))

/-- A pending lane receives its acknowledgement from the correction credits of its visit, in
any execution with the same trace and objects. -/
theorem ackReadyInCopy {p : Params} {l : Launch} {m : Mem0} {X Y : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) (hT : Y.tr = X.tr) (hO : Y.objects = X.objects)
    {g visit : Nat} (hg : g < l.threads) {warp : Fin 8} (hw : warp.val = warpIndex l g)
    (credits : Protocol.Statistics.TerminalCorrectionCredits l X (g/l.block) (stageOf warp)
      visit) (site : Fin 10)
    (hSite : waitLoc l g (stageOf warp) site = Correction.statsCreditLoc l (g/l.block)
      (stageOf warp)) :
    (Y.tr g).countP Scores.creditAcquired = visit+1 →
      OpeningPollReady Y (waitLoc l g (stageOf warp) site) (visit%2) := by
  intro pending
  have hStage : warpIndex l g/4 = (stageOf warp).val := by rw [← hw]; rfl
  rw [hT] at pending
  have h := ackReadyForPendingLane hp hMax frame hg (stageOf warp) hStage credits site hSite
    pending
  unfold OpeningPollReady at h ⊢
  rwa [hO]

private theorem creditOrder {X Y : Execution} (hT : Y.tr = X.tr) {g i j c : Nat}
    (hi : ((Y.tr g).take i).countP Scores.creditAcquired = c)
    (hj : ((X.tr g).take j).countP Scores.creditAcquired = c+1) : i < j := by
  apply lt_of_countP_take_lt (X := X) (g := g) (mark := Scores.creditAcquired)
  rw [hT] at hi
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X Y₁ Y₂ : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hMax₂ : Maximal l kernel Assumptions.all m Y₂)
    (hT₂ : Y₂.tr = X.tr) (hO₂ : Y₂.objects = X.objects) (frame : OutputFootprint p X) {g : Nat}
    (hg : g < l.threads) {warp : Fin 8} (hw : warp.val = warpIndex l g)
include hp hMax hMax₂ hT₂ hO₂ frame hg hw

/-- A biased lane at its correction join takes the credit of its visit and reaches the next
head or the terminal statistics. -/
theorem biasedLaneNext {trips split visit block floor counter bars elects start nextBlock : Nat}
    {maximum : Option ℝ} {sum : ℝ} {bias : Nat → Option ℝ} {dot : Nat → ℝ}
    (head : BiasedLoopHead p l X g warp visit block floor counter bars elects maximum sum)
    (hCounter : counter = 2^32-(trips-split)+(visit-1)) (hSplit : head.split = split)
    (hVisit : 1 ≤ visit) (hLt : visit < trips-split) (hTrips : trips < 2^31)
    (J : BiasedVisitJoin p l Y₁ Y₂ g warp visit start nextBlock counter bars elects maximum sum
      bias dot) (hOrder : head.cursor.pos < J.join.cursor.pos)
    (credits : Protocol.Statistics.TerminalCorrectionCredits l X (g/l.block) (stageOf warp) visit) :
    ∃ pos, J.join.cursor.pos < pos ∧
      LoopNextAt p l X trips split g warp visit bars elects pos := by
  have hBound : counter < 2^32 := by omega
  have hReady := ackReadyInCopy hp hMax frame hT₂ hO₂ hg hw credits
    Repeated.biased.correctionSite rfl
  obtain ⟨at',_,hs',_⟩ := BiasedVisitJoin.nextOfPending hp hMax hMax₂ hT₂ hg hw head J hOrder hBound
    hReady
  have hNext : (counter+1)%2^32 = 2^32-(trips-split)+visit := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  generalize hnx : (counter+1)%2^32 = nx at at' hs'
  rw [hNext] at hnx
  subst nx
  have hOrd : J.join.cursor.pos < at'.cursor.pos :=
    creditOrder hT₂ J.counts.2.2.2.2.1 at'.counts.2.2.2.2.1
  refine ⟨at'.cursor.pos,hOrd,?_⟩
  by_cases hMore : visit+1 < trips-split
  · have hNe : 2^32-(trips-split)+visit ≠ 2^32-1 := by omega
    generalize hpc : (if 2^32-(trips-split)+visit ≠ 2^32-1 then 5032
      else (scoreLoopSite .biased).increment+4) = pc at at' hs' hOrd
    rw [ite_eq_left hNe] at hpc
    subst pc
    exact ⟨fun _ => .inl ⟨hMore,_,_,_,_,_,by omega,at'.head,rfl,hs'.trans hSplit⟩,
      fun h => by omega⟩
  · have hEq : 2^32-(trips-split)+visit = 2^32-1 := by omega
    generalize hpc : (if 2^32-(trips-split)+visit ≠ 2^32-1 then 5032
      else (scoreLoopSite .biased).increment+4) = pc at at' hs' hOrd
    rw [ite_eq_right (fun h => h hEq)] at hpc
    subst pc
    rcases at'.exitOfLoop hp hw with ⟨hZero,⟨term⟩⟩ | ⟨hZero,head2,hPos⟩
    · have hTrips : visit+1 = trips := by have := hs'.trans hSplit; omega
      refine ⟨fun h => by omega,fun _ => ?_⟩
      rw [← hTrips]
      exact ⟨_,_,⟨term⟩⟩
    · have hs := hs'.trans hSplit
      refine ⟨fun hT => .inr ⟨by omega,_,_,_,_,?_,?_,head2,hPos⟩,fun h => ?_⟩
      · rw [hs]; omega
      · omega
      · exfalso; rw [hs] at hZero; omega

/-- A plain lane at its correction join takes the credit of its visit and reaches the next
head or the terminal statistics. -/
theorem plainLaneNext {trips split visit counter tc bars elects start : Nat} {maximum : Option ℝ}
    {sum : ℝ} (head : PlainLoopAt p l X g warp 6661 visit counter tc bars elects maximum sum)
    (hCounter : counter = 2^32-split+(visit-(trips-split)))
    (hTc : tc = 11*(trips-split)+14*(visit-(trips-split))) (hGe : trips-split ≤ visit)
    (hLt : visit < trips) (hTrips : trips < 2^31) (hSplitLe : split ≤ trips)
    (J : PlainVisitJoin p l Y₁ Y₂ g warp visit start counter tc bars elects maximum sum)
    (hOrder : head.cursor.pos < J.join.cursor.pos)
    (credits : Protocol.Statistics.TerminalCorrectionCredits l X (g/l.block) (stageOf warp) visit) :
    ∃ pos, J.join.cursor.pos < pos ∧
      LoopNextAt p l X trips split g warp visit bars elects pos := by
  have hBound : counter < 2^32 := by omega
  have hReady := ackReadyInCopy hp hMax frame hT₂ hO₂ hg hw credits
    Repeated.unbiased.correctionSite rfl
  obtain ⟨at'⟩ := PlainVisitJoin.nextOfPending hp hMax hMax₂ hT₂ hg hw head J hOrder hBound
    hReady
  have hOrd : J.join.cursor.pos < at'.cursor.pos :=
    creditOrder hT₂ J.counts.2.2.2.2.1 at'.counts.2.2.2.2.1
  refine ⟨at'.cursor.pos,hOrd,?_⟩
  by_cases hMore : visit+1 < trips
  · have hNe : (counter+1)%2^32 ≠ 0 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    generalize hpc : (if (counter+1)%2^32 ≠ 0 then 6661
      else (scoreLoopSite .plain).increment+4) = pc at at' hOrd
    rw [ite_eq_left hNe] at hpc
    subst pc
    refine ⟨fun _ => .inr ⟨by omega,_,_,_,_,?_,?_,at',rfl⟩,fun h => by omega⟩
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · omega
  · have hZero : (counter+1)%2^32 = 0 := by
      have e : counter+1 = 2^32 := by omega
      rw [e,Nat.mod_self]
    generalize hpc : (if (counter+1)%2^32 ≠ 0 then 6661
      else (scoreLoopSite .plain).increment+4) = pc at at' hOrd
    rw [ite_eq_right (fun h => h hZero)] at hpc
    subst pc
    have hTrips' : visit+1 = trips := by omega
    refine ⟨fun h => by omega,fun _ => ?_⟩
    rw [← hTrips']
    exact ⟨_,_,⟨at'.terminal⟩⟩

end PTX.Kernels.TmlFa4Fwd.Progress

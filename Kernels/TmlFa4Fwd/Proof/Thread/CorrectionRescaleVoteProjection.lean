-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescalePass
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotStages
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

private theorem correctionProjectionCountBefore {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) :
    (rescaleVoteLabels ((X.tr g).take j)).length =
      ((X.tr g).take j).countP (isRescaleStageVote 0) +
        ((X.tr g).take j).countP (isRescaleStageVote 1) := by
  apply rescaleVoteLabelsCount
  intro x hMem hSite
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hMem
  have hLT := ((List.getElem?_eq_some_iff.mp hi).1).trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hLT] at hi
  obtain ⟨a,word,hV⟩ := recordedAtRescaleVoteSite hX hi hSite
    (earlierRescaleEventNotFault hX hi he hLT)
  exact ⟨_,a,word,hV⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem correctionProjectionCursorBalance (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles votes : Nat} {ends : Nat → Option TState} {lane j : Nat} {e : Event}
    (cur : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch) shuffles votes ends)
    (hFollow : WarpFollowsEvent l X g cur.pos lane j e) (hLate : e.pc < 8447) :
    let thread := warpLane l g lane
    ((X.tr thread).take j).countP isFullWarpVote +
      (((X.tr thread).take (cur.pos lane)).countP (isRescaleStageVote 0) +
       ((X.tr thread).take (cur.pos lane)).countP (isRescaleStageVote 1)) =
      votes + (rescaleVoteLabels ((X.tr thread).take j)).length := by
  dsimp only
  let thread := warpLane l g lane
  have hRank := correctionRescaleVoteOrdinalFromActive hX cur hFollow hLate
  have hLength := correctionProjectionCountBefore hX hFollow.get
  have hSplit := List.take_add (l := X.tr thread) (i := cur.pos lane) (j := j-cur.pos lane)
  rw [Nat.add_sub_of_le hFollow.before] at hSplit
  conv at hLength =>
    rhs
    rw [hSplit, List.countP_append, List.countP_append]
  dsimp only at hRank
  dsimp only [thread] at hLength
  omega

private theorem warpBallotCounts (site mask : Nat) (a : Bool) (word : BitVec 32) :
    isWarpVote mask ⟨site,.vote mask a word⟩ = true := by simp [isWarpVote,voteClass]

private theorem projectedBallotExact {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g n : Nat}
    {stage : Fin 2} {word : BitVec 32}
    (hEntry : (rescaleVoteLabels (X.tr g))[n]? = some (stage,word)) :
    ∃ j site bit, X.get (g,j) = some ⟨site,.vote (2^32-1) bit word⟩ ∧
      site = (if stage = 0 then 8009 else 8228) ∧
      (rescaleVoteLabels ((X.tr g).take j)).length = n := by
  obtain ⟨j,site,mask,bit,hGet,hSite,hLen⟩ := rescaleVoteLabelsEntry hEntry
  have hSites : site = 8009 ∨ site = 8228 := by rw [hSite]; fin_cases stage <;> simp
  obtain ⟨_,_,hV⟩ := recordedAtRescaleVoteSite hX hGet hSites (by intro _ h; cases h)
  injection hV with hMask
  subst mask
  exact ⟨j,site,bit,hGet,hSite,hLen⟩

private theorem projectedBallotAfterCursor {X : Execution} {g j start site a : Nat}
    {bit : Bool} {word : BitVec 32}
    (hGet : X.get (g,j) = some ⟨site,.vote a bit word⟩)
    (hSite : site = 8009 ∨ site = 8228)
    (hZero : ∀ stage : Fin 2, ((X.tr g).take start).countP (isRescaleStageVote stage) = 0) :
    start ≤ j := by
  by_contra! hOrder
  have hSome : ∃ stage : Fin 2,
      isRescaleStageVote stage ⟨site,.vote a bit word⟩ = true := by
    rcases hSite with rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  obtain ⟨stage,hStage⟩ := hSome
  have hCount := countP_take_succ hGet hStage
  have hMono := countP_take_mono (isRescaleStageVote stage) (X.tr g)
    (show j+1 ≤ start by omega)
  have hEmpty := hZero stage
  change ((X.tr g).take (j+1)).countP (isRescaleStageVote stage) =
    ((X.tr g).take j).countP (isRescaleStageVote stage)+1 at hCount
  omega

/-- A ballot's position in the correction list plus the cursor's vote base is its absolute
full-warp vote ordinal. The cursor precedes both rescale stages. -/
theorem correctionProjectedBallotOrdinal (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles votes : Nat} {ends : Nat → Option TState} {lane n : Nat} {stage : Fin 2}
    {word : BitVec 32}
    (cur : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch) shuffles votes ends)
    (hLane : lane < 32)
    (hNoExit : ∀ lane < 32, ∀ j < cur.pos lane, ∀ pc, X.get (warpLane l g lane,j) ≠ some ⟨pc,.exit⟩)
    (hEmpty : ∀ stage : Fin 2,
      ((X.tr (warpLane l g lane)).take (cur.pos lane)).countP (isRescaleStageVote stage) = 0)
    (hEntry : (rescaleVoteLabels (X.tr (warpLane l g lane)))[n]? = some (stage,word)) :
    ∃ j site bit, X.get (warpLane l g lane,j) = some ⟨site,.vote (2^32-1) bit word⟩ ∧
      site = (if stage = 0 then 8009 else 8228) ∧
      X.MaskK voteClass (warpLane l g lane,j) (2^32-1) (votes+n) ∧
      (rescaleVoteLabels ((X.tr (warpLane l g lane)).take j)).length = n := by
  obtain ⟨j,site,bit,hGet,hSite,hLen⟩ := projectedBallotExact hX hEntry
  have hSites : site = 8009 ∨ site = 8228 := by rw [hSite]; fin_cases stage <;> simp
  have hBefore := projectedBallotAfterCursor hGet hSites hEmpty
  have hFollow : WarpFollowsEvent l X g cur.pos lane j ⟨site,.vote (2^32-1) bit word⟩ :=
    ⟨hLane,hGet,hBefore,hNoExit⟩
  have hLate : site < 8447 := by rcases hSites with h | h <;> omega
  have hBalance := correctionProjectionCursorBalance hX cur hFollow hLate
  dsimp only at hBalance
  rw [hEmpty 0,hEmpty 1,hLen] at hBalance
  have hCount : ((X.tr (warpLane l g lane)).take j).countP isFullWarpVote = votes+n := by
    omega
  exact ⟨j,site,bit,hGet,hSite,⟨⟨_,_,hGet,rfl,rfl⟩,hCount⟩,hLen⟩

/-- If a peer's first correction ballot is at or beyond this cursor's absolute vote base,
it is exactly at the base. This identifies the common base without requiring that the two
observed lane prefixes end at the same checkpoint. -/
theorem correctionPeerFirstBallotAtBase (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles votes : Nat} {ends : Nat → Option TState} {lane j ordinal site : Nat}
    {bit : Bool} {word : BitVec 32}
    (cur : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch) shuffles votes ends)
    (hLane : lane < 32)
    (hNoExit : ∀ lane < 32, ∀ j < cur.pos lane, ∀ pc, X.get (warpLane l g lane,j) ≠ some ⟨pc,.exit⟩)
    (hGet : X.get (warpLane l g lane,j) = some ⟨site,.vote (2^32-1) bit word⟩)
    (hSite : site = 8009 ∨ site = 8228)
    (hFirst : (rescaleVoteLabels ((X.tr (warpLane l g lane)).take j)).length = 0)
    (hOrd : X.MaskK voteClass (warpLane l g lane,j) (2^32-1) ordinal) (hBase : votes ≤ ordinal) :
    votes = ordinal := by
  let thread := warpLane l g lane
  have hOrd' : ((X.tr thread).take j).countP isFullWarpVote = ordinal := hOrd.2
  have hBefore : cur.pos lane ≤ j := by
    by_contra! h
    have hStep := countP_take_succ (p := isFullWarpVote) hGet (warpBallotCounts site _ bit word)
    have hMono := countP_take_mono isFullWarpVote (X.tr thread) (show j+1 ≤ cur.pos lane by omega)
    have hAt := cur.ordinals.vote lane hLane
    change ((X.tr thread).take (j+1)).countP isFullWarpVote =
      ((X.tr thread).take j).countP isFullWarpVote+1 at hStep
    change ((X.tr thread).take (cur.pos lane)).countP isFullWarpVote = votes at hAt
    omega
  have hFollow : WarpFollowsEvent l X g cur.pos lane j ⟨site,.vote (2^32-1) bit word⟩ :=
    ⟨hLane,hGet,hBefore,hNoExit⟩
  have hLate : site < 8447 := by rcases hSite with h | h <;> omega
  have hBalance := correctionProjectionCursorBalance hX cur hFollow hLate
  dsimp only at hBalance
  rw [hOrd',hFirst] at hBalance
  omega

end PTX.Kernels.TmlFa4Fwd.Thread

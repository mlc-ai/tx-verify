-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotAgreement
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.CorrectionLseFallback
import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

private def betweenBallots (pc : Nat) : Bool := decide (8009 < pc ∧ pc ≤ 8228)

private def stageBallotStepCode (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || ordinaryEvent i.op) &&
    match i.op with
    | .bra dst _ => decide (7932 ≤ dst) && (betweenBallots pc == betweenBallots dst)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem stageBallotAudit :
    ((kernel.code.drop 7932).zipIdx 7932).all (fun (i,pc) => stageBallotStepCode pc i) = true :=
  by decide +kernel

private theorem stageBallotCodeAt {pc : Nat} {i : Instr} (hLo : 7932 ≤ pc)
    (hc : kernel.code[pc]? = some i) : stageBallotStepCode pc i = true := by
  apply List.all_eq_true.mp stageBallotAudit (i,pc)
  apply List.mem_of_getElem? (i := pc-7932)
  rw [List.getElem?_zipIdx, List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  rfl

private def pendingStageOne (pc : Nat) : Nat := if betweenBallots pc then 1 else 0

private theorem ballotDifferenceOfLocal {l : Launch} {g : Nat} {s u : TState}
    (hLo : 7932 ≤ s.pc) (ht : Tau kernel Assumptions.all l g s u) :
    7932 ≤ u.pc ∧ pendingStageOne s.pc = pendingStageOne u.pc := by
  have hNot (h : s.pc ∈ Assumptions.swExp2Sites) : False := by
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at h
    omega
  obtain ⟨i,hc,_,hSource⟩ := correctionTauFrame hNot ht
  have hNotZero : s.pc ≠ 8009 := by
    intro hs
    rw [hs,Flow.code_8009] at hc
    obtain rfl := Option.some.inj hc
    rcases hSource with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
    · cases hGuard
    · cases hLocal
  have hNotOne : s.pc ≠ 8228 := by
    intro hs
    rw [hs,Flow.code_8228] at hc
    obtain rfl := Option.some.inj hc
    rcases hSource with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
    · cases hGuard
    · cases hLocal
  have hNext (hp : u.pc = s.pc+1) : 7932 ≤ u.pc ∧
      pendingStageOne s.pc = pendingStageOne u.pc := by
    have hEq : (8009 < u.pc ∧ u.pc ≤ 8228) ↔ (8009 < s.pc ∧ s.pc ≤ 8228) := by omega
    exact ⟨by omega, by simp [pendingStageOne, betweenBallots, hEq]⟩
  rcases hSource with ⟨rfl,_⟩ | ⟨_,_,hFrame⟩
  · exact hNext rfl
  · have hp := hFrame.pc
    have hAudit := (Bool.and_eq_true_iff.mp (stageBallotCodeAt hLo hc)).2
    cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hp
    case bra dst uni =>
      simp only [hop, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hAudit
      exact ⟨hp.symm ▸ hAudit.1, by simp [pendingStageOne, hp, hAudit.2]⟩
    case brx => simp [hop] at hAudit
    all_goals exact hNext hp

private theorem ballotDifferenceOfEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 7932 ≤ s.pc) (he : EStep kernel Assumptions.all l g s e (some u)) :
    7932 ≤ u.pc ∧
      (if isRescaleStageVote 0 e then 1 else 0) + pendingStageOne s.pc =
        (if isRescaleStageVote 1 e then 1 else 0) + pendingStageOne u.pc := by
  have hE := estep_source_pc he
  by_cases hZero : s.pc = 8009
  · have hp := rescaleVoteContinues 0 hZero he
    have hu : u.pc = 8010 := by omega
    rw [hu,hZero]
    exact ⟨by decide, by simp [isRescaleStageVote, correctionRescaleMarkPc, barrierMark,
      pendingStageOne, betweenBallots, hE, hZero]⟩
  by_cases hOne : s.pc = 8228
  · have hp := rescaleVoteContinues 1 hOne he
    have hu : u.pc = 8229 := by omega
    rw [hu,hOne]
    exact ⟨by decide, by simp [isRescaleStageVote, correctionRescaleMarkPc, barrierMark,
      pendingStageOne, betweenBallots, hE, hOne]⟩
  obtain ⟨i,hc,hNotLoc,hFire⟩ := estep_event_source he
  have hCode := (Bool.and_eq_true_iff.mp (stageBallotCodeAt hLo hc)).1
  rw [hNotLoc,Bool.false_or] at hCode
  have hFrame := callbackFrame_fires (ordinaryEventFrame hCode) hFire
  have hEq : (8009 < u.pc ∧ u.pc ≤ 8228) ↔ (8009 < s.pc ∧ s.pc ≤ 8228) := by
    rcases hFrame with h | h <;> omega
  refine ⟨by rcases hFrame with h | h <;> omega, ?_⟩
  simp [isRescaleStageVote, correctionRescaleMarkPc, barrierMark, pendingStageOne,
    hE, hZero, hOne, betweenBallots, hEq]

private theorem stageBallotDifference {l : Launch} {g : Nat} {s t : TState} {es : List Event}
    (h : TraceReach kernel Assumptions.all l g s es t) (hLo : 7932 ≤ s.pc) :
    es.countP (isRescaleStageVote 0) + pendingStageOne s.pc =
      es.countP (isRescaleStageVote 1) + pendingStageOne t.pc := by
  induction h with
  | refl => rfl
  | tau ht _ ih =>
    obtain ⟨hu,hDiff⟩ := ballotDifferenceOfLocal hLo ht
    rw [hDiff]
    exact ih hu
  | event he _ ih =>
    obtain ⟨hu,hDiff⟩ := ballotDifferenceOfEvent hLo he
    have hh := ih hu
    simp only [List.countP_cons]
    omega

/-- An actual rescale site's stage is fixed by the parity of its ballot ordinal
relative to the active correction warp's shared scheduler cursor. -/
theorem correctionRescaleBallotStageOfOrdinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles votes : Nat} {ends : Nat → Option TState}
    {lane j : Nat} {e : Event}
    (cur : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
      shuffles votes ends) (hFollow : WarpFollowsEvent l X g cur.pos lane j e)
    (hSite : e.pc = 8009 ∨ e.pc = 8228) :
    (((X.tr (warpLane l g lane)).take j).countP isFullWarpVote - votes) % 2 =
      if e.pc = 8009 then 0 else 1 := by
  have hLate : e.pc < 8447 := by rcases hSite with h | h <;> omega
  have hOrd := correctionRescaleVoteOrdinalFromActive hX cur hFollow hLate
  dsimp only at hOrd
  have hAt := cur.checkpoint lane hFollow.lane
  have hRun := (cur.continuation lane hFollow.lane).after_local_nonempty
    (cur.localSteps lane hFollow.lane) hFollow.nonempty
  have hGet : ((X.tr (warpLane l g lane)).drop (cur.pos lane))[j-cur.pos lane]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hFollow.before]
    exact hFollow.get
  obtain ⟨t,_,hReach,hEvent⟩ := hRun.before_event hGet
  have hPc := estep_source_pc hEvent
  have hDiff := stageBallotDifference hReach hAt.1.ge
  rw [hAt.1, ← hPc] at hDiff
  have hStart : pendingStageOne 7932 = 0 := rfl
  rcases hSite with h0 | h1
  · rw [h0] at hDiff ⊢
    have hp : pendingStageOne 8009 = 0 := rfl
    simp only [hStart, hp, Nat.add_zero, ↓reduceIte] at hDiff ⊢
    omega
  · rw [h1] at hDiff ⊢
    have hp : pendingStageOne 8228 = 1 := rfl
    have hNe : (8228 : Nat) ≠ 8009 := by decide
    simp only [hStart, hp, Nat.add_zero, hNe, ↓reduceIte] at hDiff ⊢
    omega

private theorem ballotHasMask (site mask : Nat) (a : Bool) (word : BitVec 32) :
    isWarpVote mask ⟨site,.vote mask a word⟩ = true := by
  simp [isWarpVote,voteClass]

/-- Two actual correction votes with the same full-mask ordinal use the same stage
instruction and return the same rescale decision word. -/
theorem correctionRescaleBallotPeersAgree {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g h i j k site site' : Nat} {a a' : Bool} {word word' : BitVec 32}
    (hWarp : SameWarp l g h) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hUsedK : ∀ b < p.batch, ∀ byte < 4, ∀ w acc bs, X.MemWrites w acc bs →
      ¬ acc.Covers ((globalLoc (p.usedKBase+4*b)).at byte))
    (he : X.get (g,i) = some ⟨site,.vote (2^32-1) a word⟩)
    (hf : X.get (h,j) = some ⟨site',.vote (2^32-1) a' word'⟩)
    (hSite : site = 8009 ∨ site = 8228) (hSite' : site' = 8009 ∨ site' = 8228)
    (hi : X.MaskK voteClass (g,i) (2^32-1) k) (hj : X.MaskK voteClass (h,j) (2^32-1) k) :
    site = site' ∧ word = word' := by
  let l0 := laneOf l g
  let l1 := laneOf l h
  have hg := event_thread_lt hX he
  have hLane0 : l0 < 32 := Nat.mod_lt _ (by decide)
  have hLane1 : l1 < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g l0 = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hPeer : warpLane l g l1 = h := Step.warpLane_of_sameWarp hWarp
  have hlo : 7988 < site := by rcases hSite with hh | hh <;> omega
  have hhi : site < 8447 := by rcases hSite with hh | hh <;> omega
  have hGet : X.get (warpLane l g l0,i) = some ⟨site,.vote (2^32-1) a word⟩ := hSelf.symm ▸ he
  have hWork := correctionWorkOfLateEvent hp hX hg hLo hHi hLane0
    (show 7859 < site by omega) (show site < 9201 by omega) hGet
  obtain ⟨batch,hb,hCtaLo,hCtaHi,ends,shuffles,votes,cur,hStart⟩ :=
    correctionActiveTileOfEvent hp hX hg hLo hHi hLane0 hWork (show 7884 < site by omega) hGet
  have hLeftCount := correctionRescaleVoteOrdinalFromActive hX cur hStart hhi
  have hiCount : ((X.tr g).take i).countP isFullWarpVote = k := hi.2
  rw [hSelf, hiCount] at hLeftCount
  have hk : votes ≤ k := by dsimp only at hLeftCount; omega
  have hjCount : ((X.tr h).take j).countP isFullWarpVote = k := hj.2
  have hBefore : cur.pos l1 ≤ j := by
    by_contra! hOrder
    have hAdd := countP_take_succ (p := isFullWarpVote) hf (ballotHasMask site' _ a' word')
    have hMono := countP_take_mono isFullWarpVote (X.tr h)
      (show j+1 ≤ cur.pos l1 by omega)
    have hAt := cur.ordinals.vote l1 hLane1
    rw [hPeer] at hAt
    omega
  have hFollow' : WarpFollowsEvent l X g cur.pos l1 j ⟨site',.vote (2^32-1) a' word'⟩ :=
    ⟨hLane1, hPeer.symm ▸ hf, hBefore, hStart.noExit⟩
  have hParity := correctionRescaleBallotStageOfOrdinal hX cur hStart hSite
  have hParity' := correctionRescaleBallotStageOfOrdinal hX cur hFollow' hSite'
  rw [hSelf, hiCount] at hParity
  rw [hPeer, hjCount] at hParity'
  have hSame : site = site' := by
    have hCases := hParity.symm.trans hParity'
    rcases hSite with rfl | rfl <;> rcases hSite' with rfl | rfl
    · rfl
    · cases hCases
    · cases hCases
    · rfl
  exact ⟨hSame, CorrectionRescaleBallot.wordsAgree hp hX hWarp hLo hHi hUsedK
    (CorrectionRescaleBallot.ofEvent hSite he) (CorrectionRescaleBallot.ofEvent hSite' hf) hi hj⟩

end PTX.Kernels.TmlFa4Fwd.Thread

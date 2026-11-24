-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.StaticSafety
public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.AsyncCopy PTX.MBarrier Prologue

/-- The barrier for a stage's completed QK accumulator. -/
def firstScoreObject (l : Launch) (cta : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + (80 + 8 * stage.val)⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem scoreCommitSiteOfTarget {commit : EvId} {pc cta : Nat} {s : TcCommit.Spec}
    {rank : Fin 16} (stage : Fin 2) (he : X.get commit = some ⟨pc, .tc (.commit s)⟩)
    (ht : TcCommit.target s rank = some (firstScoreObject l cta stage)) :
    (∃ block : Fin 4, pc = (Mma.commitSite (Mma.qkCommitSite block)).pc) ∧
      commit.1 / l.block = cta := by
  rcases inCommitSites hX he with hFixed | hRing
  · have hLoc := Mma.mmaFixedCommitExactAddress hp hX he hFixed ht
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (80 + 8 * stage.val) =
      l.sharedBase + Mma.fixedMmaCommitOffset pc at hAddr
    have hStage := stage.isLt
    refine ⟨?_, (congrArg Loc.cta hLoc).symm⟩
    simp only [fixedCommits, List.mem_cons, List.not_mem_nil, or_false] at hFixed
    rcases hFixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · simp [Mma.fixedMmaCommitOffset] at hAddr; omega
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    all_goals simp [Mma.fixedMmaCommitOffset] at hAddr; omega
  · obtain ⟨slot, hLoc⟩ := Mma.mmaRingCommitAddress hp hX he hRing ht
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (80 + 8 * stage.val) = l.sharedBase + (8 * slot.val + 56) at hAddr
    have := slot.isLt
    omega

private theorem scoreUnitRecord {cta : Nat} {r : Record Ref} (stage : Fin 2)
    (hr : r ∈ X.objects (firstScoreObject l cta stage)) (hu : r.action.units ≠ 0) :
    ∃ (block : Fin 4), ∃ commit s rank, r.id = .async commit (.tcNotify rank) ∧
      X.get commit = some ⟨(Mma.commitSite (Mma.qkCommitSite block)).pc, .tc (.commit s)⟩ ∧
      commit.1 / l.block = cta ∧ TcCommit.target s rank = some (firstScoreObject l cta stage) := by
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ h => simp [h, Action.units] at hu
  | wait _ _ h => simp [h, Action.units] at hu
  | inval _ _ h => simp [h, Action.units] at hu
  | arrive _ he _ =>
    obtain ⟨off, hOff, hLoc⟩ := actualArriveOffsetIn hp hX he
    have hAddr : l.sharedBase + (80 + 8 * stage.val) = l.sharedBase + off := congrArg Loc.addr hLoc
    fin_cases stage <;> simp only [ordinaryArriveOffsets, List.mem_cons, List.not_mem_nil,
      or_false] at hOff <;> simp at hAddr <;> omega
  | increment _ _ h => simp [h, Action.units] at hu
  | tensor _ _ _ h => simp [h, Action.units] at hu
  | arriveOn _ he hm _ _ =>
    rw [hm] at he
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := Loader.actualAsyncArrival hX he
    have hs : Loader.copyCommitPc site + 1 ∈ [674, 904, 1137, 1342, 1602, 1735] := by
      fin_cases site <;> decide
    obtain ⟨off, hOff, hLoc⟩ := Loader.loaderAsyncAddress hp hX he hs
    have hAddr : l.sharedBase + (80 + 8 * stage.val) = l.sharedBase + off := congrArg Loc.addr hLoc
    fin_cases stage <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff <;>
      simp at hAddr <;> omega
  | bulk _ _ _ _ h => simp [h, Action.units] at hu
  | commit hId he ht _ =>
    obtain ⟨⟨block, hPc⟩, hCta⟩ := scoreCommitSiteOfTarget hp hX stage he ht
    exact ⟨block, _, _, _, hId, hPc ▸ he, hCta, ht⟩
  | clc _ he _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

/-- A successful score wait observes a real QK commit in its CTA. -/
theorem firstScoreWaitObservesCommit {w : EvId} {scope : MbarScope} (stage : Fin 2)
    (he : X.get w = some ⟨3425, .wait (firstScoreObject l (w.1 / l.block) stage) 0 true true scope⟩)
    :
    ∃ (block : Fin 4), ∃ commit s rank,
      X.get commit = some ⟨(Mma.commitSite (Mma.qkCommitSite block)).pc, .tc (.commit s)⟩ ∧
      SameCta l commit.1 w.1 ∧
      TcCommit.target s rank = some (firstScoreObject l (w.1 / l.block) stage) ∧
      rank ∈ X.tcNotified commit ∧
      WaitObserves X (.async commit (.tcNotify rank)) w
        (firstScoreObject l (w.1 / l.block) stage) true scope := by
  let loc := firstScoreObject l (w.1 / l.block) stage
  let log := X.objects loc
  obtain ⟨j, poll, hj, hId, ha, hClean, hSuccess⟩ := actualPollRecordClean hp hX he
  have hChecked := X.objects_checked hX loc
  obtain ⟨st, n, hSt, ha', hParity, hFinished⟩ := hChecked.okPoll hj hSuccess
  obtain rfl : n = 0 := (Action.pollParity.inj (ha'.symm.trans ha)).1
  have hPos : 0 < st.phase := by omega
  let phase := st.phase - 1
  change log[j]? = some poll at hj
  have hObserved : observedAt log j = some phase := by
    simp only [observedAt, hj, Option.bind_some, hFinished, ite_eq_left hPos, phase]
  have hNo := objects_noInval hX.tma.2.2.1 (fun e _ => noMbarInval hX (i := e)) loc
  have hLen : j < log.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨q, hq, hCompletion⟩ := hChecked.crossing hNo hLen.le hSt
    (show phase < st.phase by dsimp [phase]; omega)
  have hUnits := (hChecked.completion_sums hNo (hq.trans hLen) hCompletion).2
  obtain ⟨index, _, hNonzero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hUnits)
  have ⟨hPhase, hUnits'⟩ : phaseAt log index = some phase ∧ unitsAt log index ≠ 0 := by
    simpa [log, apply_ite] using hNonzero
  obtain ⟨rec, hr⟩ : ∃ rec, log[index]? = some rec := by
    cases hGet : log[index]? with
    | none => simp [unitsAt, hGet] at hUnits'
    | some rec => exact ⟨rec, rfl⟩
  have hRec : rec.fault = none ∧ rec.action.units ≠ 0 := by simpa [unitsAt, hr] using hUnits'
  obtain ⟨block, commit, s, rank, hNote, hc, hCta, ht⟩ :=
    scoreUnitRecord hp hX stage (List.mem_of_getElem? hr) hRec.2
  have hBefore := MbarRing.Slot.updateBeforeWait_of_phase hChecked hNo hr hRec.1 hj hClean hSuccess
    hPhase hObserved
  rw [hNote, hId] at hBefore
  have hDelivered : rank ∈ X.tcNotified commit := by
    by_contra hBad
    exact (no_tc_notification_record hX.tma.2.2.1 hBad (List.mem_of_getElem? hr)) hNote
  exact ⟨block, commit, s, rank, hc,
    ⟨event_thread_lt hX hc, event_thread_lt hX he, hCta⟩, ht, hDelivered,
    ⟨⟨3425, 0, he⟩, hBefore⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread

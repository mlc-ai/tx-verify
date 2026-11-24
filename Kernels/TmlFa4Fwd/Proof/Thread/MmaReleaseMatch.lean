-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseOrdinal
public import Kernels.TmlFa4Fwd.Proof.MmaRingMatching

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (readyObject emptyObject)

noncomputable section

/-- The issuing lane's release returns the same physical slot as its ready occurrence. -/
structure ReleaseMatch (l : Launch) (X : Execution) (g index : Nat) (form : ReleaseForm)
    (target : Loc) where
  wait : Nat
  slot : Fin 3
  parity : Nat
  earlier : wait < index
  ready : ReadyPoll l X g wait slot parity true .cta
  readyForm : ReleaseReadyObservation X g wait form (readyObject l g slot) parity
  target_eq : target = emptyObject l g slot
  ordinal : readyOccurrence X g wait form = releaseOccurrence X g index form
  resumes : Resumes kernel X (g, wait) (g, index)

/-- A real K/V release names the physical slot of its exact ready occurrence. -/
theorem ReleaseIssue.matchReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {form : ReleaseForm} {spec : TcCommit.Spec} {rank : Fin 16} {target : Loc}
    (he : ReleaseIssue X g index form spec) (hTarget : TcCommit.target spec rank = some target) :
    Nonempty (ReleaseMatch l X g index form target) := by
  cases form with
  | firstKey =>
    have hLoc := initialEmptyReleaseAddress hp hX he hTarget
    obtain ⟨hI, inst, leader, hE⟩ := readyReleaseElection hp hX 0 he
    obtain ⟨j, hj, ready, parity, acquire, scope, hPoll, hOrdinal⟩ :=
      releaseElectionWaitOrdinal hp hX 0 hE
    obtain ⟨rfl, rfl, rfl, rfl⟩ := initialReadyPollOperands hp hX hPoll
    obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hPoll
    have hLt : j < index := by omega
    have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    have hBefore : TraceBefore X (g, j) (g, index) := ⟨rfl, hLt, hLen⟩
    have hResume : Resumes kernel X (g, j) (g, index) := by
      refine ⟨hBefore, ?_⟩
      simp only [hPoll, Option.map_some, Kind.resume]
      exact ⟨_, exit, _, 0, true, .cta, hPoll, hSpin, hBefore⟩
    exact ⟨⟨j, 0, 0, hLt, ⟨_, hPoll, rfl⟩, hPoll, hLoc, hOrdinal, hResume⟩⟩
  | loopValue =>
    obtain ⟨j, hj, slot, parity, ht, hPoll, ho, hResumes⟩ :=
      recurringReleaseMatchesReady hp hX 0 he hTarget
    exact ⟨⟨j, slot, parity, hj, ⟨_, hPoll, rfl⟩, hPoll, ht, ho, hResumes⟩⟩
  | loopKey =>
    obtain ⟨j, hj, slot, parity, ht, hPoll, ho, hResumes⟩ :=
      recurringReleaseMatchesReady hp hX 1 he hTarget
    exact ⟨⟨j, slot, parity, hj, ⟨_, hPoll, rfl⟩, hPoll, ht, ho, hResumes⟩⟩
  | tailValue =>
    obtain ⟨j, hj, slot, parity, ht, hPoll, ho, hResumes⟩ :=
      recurringReleaseMatchesReady hp hX 2 he hTarget
    exact ⟨⟨j, slot, parity, hj, ⟨_, hPoll, rfl⟩, hPoll, ht, ho, hResumes⟩⟩

/-- Distinct releases by one issuer match distinct ready acquisitions. -/
theorem ReleaseMatch.issue_eq_of_wait_eq {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {form form' : ReleaseForm} {spec spec' : TcCommit.Spec} {target target' : Loc}
    (ha : ReleaseIssue X g i form spec) (hb : ReleaseIssue X g j form' spec')
    (a : ReleaseMatch l X g i form target) (b : ReleaseMatch l X g j form' target')
    (hWait : a.wait = b.wait) : i = j := by
  have hReady := a.readyForm
  rw [hWait] at hReady
  obtain rfl := hReady.form_eq b.readyForm
  have hOrd : releaseOccurrence X g i form = releaseOccurrence X g j form := by
    rw [← a.ordinal, ← b.ordinal, hWait]
  obtain ⟨hi, inst, leader, hElect⟩ := readyReleaseElection hp hX (releaseIndex form) ha
  obtain ⟨hj, inst', leader', hElect'⟩ := readyReleaseElection hp hX (releaseIndex form) hb
  let selected := ElectOrd.atSites (fun site => site == (slotElect (releaseIndex form)).pc)
  have haIdx := nthEv_eq (p := selected) hElect (by simp [selected, ElectOrd.atSites, isElectEv,
    slotElect])
  have hbIdx := nthEv_eq (p := selected) hElect' (by simp [selected, ElectOrd.atSites, isElectEv,
    slotElect])
  change nthEv X selected g (releaseOccurrence X g i form) = i - 1 at haIdx
  change nthEv X selected g (releaseOccurrence X g j form) = j - 1 at hbIdx
  rw [hOrd, hbIdx] at haIdx
  omega

/-- A release depends on each successful acquisition of its slot at or before the matched
acquisition's ordinal on its issuing lane. -/
theorem ReleaseMatch.resumesOfEarlierReady {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g index wait parity : Nat} {form : ReleaseForm} {target : Loc}
    (a : ReleaseMatch l X g index form target)
    (hPoll : ReadyPoll l X g wait a.slot parity true .cta)
    (hOrd : (atPrefix l X g wait).kvAcquires a.slot ≤
      (atPrefix l X g a.wait).kvAcquires a.slot) :
    Resumes kernel X (g, wait) (g, index) := by
  have hEarlier : wait ≤ a.wait := by
    by_contra! hLater
    have hStep := a.ready.step.1
    have hMono := MbarRing.Poll.okPolls_mono (readyObject l g a.slot) (X.tr g)
      (show a.wait + 1 ≤ wait by omega)
    simp only [atPrefix, kvAcquireCount, readyObject] at hStep hOrd hMono
    omega
  obtain ⟨⟨site, kind⟩, hEvent, hKind⟩ := hPoll
  dsimp only at hKind
  subst kind
  obtain ⟨next, hSpin⟩ := actualCanonicalPoll hX hEvent
  have hTrace : TraceBefore X (g, wait) (g, index) :=
    ⟨rfl, hEarlier.trans_lt a.earlier, a.resumes.1.2.2⟩
  refine ⟨hTrace, ?_⟩
  simp only [hEvent, Option.map_some, Kind.resume]
  exact ⟨_, next, _, parity, true, .cta, hEvent, hSpin, hTrace⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma

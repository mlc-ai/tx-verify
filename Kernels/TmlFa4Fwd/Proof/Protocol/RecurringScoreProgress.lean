-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ScorePollOrdinals
import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringScoreGate
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarCount
import Lemmas.Protocol.MbarOneShot
import Lemmas.Protocol.MbarRingBlocker
import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Prologue Thread.Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A score commit of ordinal n needs n successful score polls by every
participating softmax lane, via the preceding joint probability generation. -/
theorem scoreCommitLeLanePolls (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (guard : CorrectionJointGuards l X) {g : Nat} (hw : warpIndex l g < 8) (stage : Fin 2)
    (hStage : warpIndex l g/4 = stage.val) {e : EvId} {spec : TcCommit.Spec} {rank : Fin 16}
    (commit : ScoreCommit l X e (g/l.block) stage spec rank) :
    scoreCommitOrdinal l X (g/l.block) stage e ≤
      Flow.okPolls (scoreReadyObject l (g/l.block) stage) (X.tr g) := by
  by_contra! later
  obtain ⟨_,_,_,_,hr,_,ok,_,observed,lower,_,_⟩ :=
    probabilityObservedBeforeScoreOrdinal hp hX commit 0 later
  obtain ⟨⟨lane,j⟩,credit,owner,age,_⟩ :=
    jointPollObservesLane hp hX guard stage rfl hw hStage hr ok observed
  change lane = g at owner
  subst lane
  obtain ⟨k,⟨pc,kind⟩,q,acq,scope,he,hKind,hOrdinal,_⟩ :=
    softmaxProbabilityCreditScorePoll hp hX stage 0 hw credit
  change kind = _ at hKind
  subst kind
  have hOne := MbarRing.Poll.okPoll_get he
  have hMono := MbarRing.Poll.okPolls_mono (scoreReadyObject l (g/l.block) stage) (X.tr g)
    (show k+1 ≤ (X.tr g).length from len_of_get he)
  rw [List.take_length,hOne,hOrdinal,age] at hMono
  omega

/-- A delivered score generation leaves the barrier exactly one phase ahead
of a lane still waiting for that generation. -/
theorem pendingScorePhaseOfNotification (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (guard : CorrectionJointGuards l X) {g n : Nat}
    (hw : warpIndex l g < 8) (stage : Fin 2) (hStage : warpIndex l g/4 = stage.val) {e : EvId}
    {spec : TcCommit.Spec} {rank : Fin 16} (commit : ScoreCommit l X e (g/l.block) stage spec rank)
    (age : scoreCommitOrdinal l X (g/l.block) stage e = n) (delivered : rank ∈ X.tcNotified e)
    (pending : Flow.okPolls (scoreReadyObject l (g/l.block) stage) (X.tr g) = n) :
    let log := X.objects (scoreReadyObject l (g/l.block) stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = n+1 := by
  classical
  let loc := scoreReadyObject l (g/l.block) stage
  let log := X.objects loc
  obtain ⟨_,he⟩ := commit.1
  have act : objectAction X X.async loc (.async e (.tcNotify rank)) = some (.arrive 1 0) := by
    simp [objectAction,he,commit.2,delivered,loc]
  obtain ⟨i,r,hr,hId,hAction⟩ := MbarOneShot.Hist.record_of_action hX act
  have init := scoreReadyInitialized hp hX stage (List.mem_of_getElem? hr)
  have noInv := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have checked := X.objects_checked hX loc
  have shape {d : Record Ref} (hd : d ∈ log) (update : CounterUpdate d.action) :
      d.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,_,_,_,action⟩ := scoreReadyUpdate hp hX stage hd update
    exact action
  obtain ⟨s,hs⟩ := MbarRing.Unit.final_of_init hX init noInv
    (List.ne_nil_of_mem (List.mem_of_getElem? hr))
  have inc : incrementsBefore log log.length = 0 := incrementsBefore_length_of log (by
    intro d hd ha
    have h := shape hd (by rw [ha]; trivial)
    rw [ha] at h
    cases h)
  have expected {k st} (h : stateBefore log k = some st) : st.expected = 1 :=
    PairTmaRing.expected_of_init hX init noInv h
  have tx := MbarRing.tx_zero_of hX noInv
    (fun d hd c t h => (Action.arrive.inj (h.symm.trans (shape hd (by rw [h]; trivial)))).2)
    (by intro d hd c ha; have h := shape hd (by rw [ha]; trivial); rw [ha] at h; cases h) le_rfl hs
  have units := MbarRing.Blocker.units_eq_phase checked noInv hs tx (expected hs) inc
  obtain ⟨clean,aligned⟩ := scoreNotificationPhaseExact hp hX stage hr
    (by rw [hAction]; trivial) hId
  obtain ⟨_,before,hBefore,_⟩ := PairTmaRing.state_of_init hX init noInv hr
    (by intro k; rw [hAction]; simp)
  have hRank : before.phase = n := by simpa only [phaseAt,hBefore,Option.map_some,
    Option.some.injEq,age] using aligned
  have low := (checked.unit_arrival_phase noInv hr hBefore hAction clean).1
  rw [expected hBefore,Nat.one_mul,hRank] at low
  have mono := unitsBefore_mono log (show i+1 ≤ log.length from
    (List.getElem?_eq_some_iff.mp hr).1)
  rw [unitsBefore_succ log hr] at mono
  change n ≤ unitsBefore log i at low
  have total : unitsBefore log log.length = s.phase := by
    simpa only [unitsBefore,List.take_length] using units
  rw [total] at mono
  have more : n+1 ≤ s.phase := by
    exact (Nat.add_le_add_right low 1).trans (by simpa [arrivalUnits,hAction,clean] using mono)
  refine ⟨s,hs,Nat.le_antisymm ?_ more⟩
  by_contra! high
  have card := checked.card_unit_arrivals_phase noInv
    (fun _ _ _ _ hd _ ha => (Action.arrive.inj
      (ha.symm.trans (shape (List.mem_of_getElem? hd) (by rw [ha]; trivial)))).1)
    (fun _ _ _ h => expected h) inc le_rfl hs high
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (card.symm ▸ Nat.zero_lt_one)
  obtain ⟨_,d,t,hd,ha,_,phase⟩ := Finset.mem_filter.mp hk
  obtain ⟨issue,sp,rk,id,comm,target,_,_⟩ :=
    scoreReadyUpdate hp hX stage (List.mem_of_getElem? hd) (by rw [ha]; trivial)
  have aligned := (scoreNotificationPhaseExact hp hX stage hd (by rw [ha]; trivial) id).2
  have bound := scoreCommitLeLanePolls hp hX guard hw stage hStage (e := issue)
    (spec := sp) (rank := rk) ⟨comm,target⟩
  rw [pending] at bound
  have eq := Option.some.inj (phase.symm.trans aligned)
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores

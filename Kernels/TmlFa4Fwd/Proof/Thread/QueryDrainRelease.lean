-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryReleaseOnce
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Lemmas.Protocol.PairTmaRing.ItemFacts
import Lemmas.Order.DependencyWitness
import Lemmas.Protocol.UnitNotify

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.MBarrier
open Thread.Output (queryObject)
open PTX.Kernels.TmlFa4Fwd.Loader

/-- An object to which the MMA lane returns one query buffer. -/
def queryEmptyObject (l : Launch) (cta : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + (16 + 8 * stage.val)⟩

/-- The return object for the second query buffer. -/
def secondQueryEmpty (l : Launch) (cta : Nat) : Loc := queryEmptyObject l cta 1

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A query-empty counter update is an actual query return on its owner CTA. -/
theorem queryEmptyUpdateAt {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (queryEmptyObject l cta stage)) (hUpdate : CounterUpdate r.action) :
    ∃ (g index : Nat) (rank : Fin 16) (spec : TcCommit.Spec),
      r.id = .async (g,index) (.tcNotify rank) ∧
      X.get (g,index) =
        some ⟨(Mma.commitSite (Mma.queryReleaseSite stage)).pc, .tc (.commit spec)⟩ ∧
      g / l.block = cta ∧ TcCommit.target spec rank = some (queryEmptyObject l cta stage) ∧
      r.action = .arrive 1 0 := by
  have offset {off owner : Nat}
      (h : queryEmptyObject l cta stage = ⟨.shared, owner, l.sharedBase + off⟩) :
      off = 16 + 8 * stage.val := by
    have hAddress := congrArg Loc.addr h
    change l.sharedBase + (16 + 8 * stage.val) = l.sharedBase + off at hAddress
    omega
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha | wait _ _ ha | inval _ _ ha => rw [ha] at hUpdate; exact hUpdate.elim
  | arrive _ he _ =>
    obtain ⟨off, hOff, hl⟩ := actualArriveOffsetIn hp hX he
    have hNo : 16 + 8 * stage.val ∉ ordinaryArriveOffsets := by fin_cases stage <;> decide
    exact (hNo (offset hl ▸ hOff)).elim
  | increment _ he _ => exact (noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor _ he hl _ =>
    obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
    obtain ⟨off, hh, ha⟩ := loaderTensorAddress hp hX site he
    have h := offset (hl.symm.trans ha)
    rw [h] at hh
    fin_cases stage <;> simp at hh
  | arriveOn _ he hl _ _ =>
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := actualAsyncArrival hX he
    have hs : copyCommitPc site + 1 ∈ [674, 904, 1137, 1342, 1602, 1735] := by
      fin_cases site <;> decide
    obtain ⟨off, hh, ha⟩ := loaderAsyncAddress hp hX he hs
    have h := offset (hl.symm.trans ha)
    rw [h] at hh
    fin_cases stage <;> simp at hh
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | @commit issue site spec rank hid he hTarget ha =>
    rcases inCommitSites hX he with hFixed | hRing
    · have hl := Mma.mmaFixedCommitExactAddress hp hX he hFixed hTarget
      have hOff := offset hl
      have hSite : site = (Mma.commitSite (Mma.queryReleaseSite stage)).pc := by
        simp only [fixedCommits, List.mem_cons, List.not_mem_nil, or_false] at hFixed
        rcases hFixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          fin_cases stage <;> simp [Mma.fixedMmaCommitOffset] at hOff <;>
          (first | omega | rfl)
      subst site
      exact ⟨_, _, _, _, hid, he, (congrArg Loc.cta hl).symm, hTarget, ha⟩
    · obtain ⟨slot, hl⟩ := Mma.mmaRingCommitAddress hp hX he hRing hTarget
      have := offset hl
      have := stage.isLt
      omega
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

/-- Every counter update to a query return object is a unit notification of the MMA commit. -/
theorem queryEmptyUpdate {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (queryEmptyObject l cta stage)) (hUpdate : CounterUpdate r.action) :
    r.action = .arrive 1 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, ha⟩ := queryEmptyUpdateAt hp hX stage hr hUpdate
  exact ha

/-- A query return object has at most one actual counter update in any consistent prefix. -/
theorem queryEmptyUpdateUnique {cta : Nat} (stage : Fin 2) {r q : Record Ref}
    (hr : r ∈ X.objects (queryEmptyObject l cta stage))
    (hq : q ∈ X.objects (queryEmptyObject l cta stage)) (hR : CounterUpdate r.action)
    (hQ : CounterUpdate q.action) : r.id = q.id := by
  obtain ⟨g, i, x, a, hId, he, hCta, hTarget, _⟩ := queryEmptyUpdateAt hp hX stage hr hR
  obtain ⟨h, j, y, b, hId', he', hCta', hTarget', _⟩ := queryEmptyUpdateAt hp hX stage hq hQ
  have hEv := Thread.Mma.queryReleaseEventUnique hp hX stage (hCta.trans hCta'.symm) he he'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEv
  rw [he] at he'
  have hSpec := TcKind.commit.inj (Kind.tc.inj (Event.mk.inj (Option.some.inj he')).2)
  subst b
  rw [hId, hId', MbarRing.Notify.rank_eq hTarget hTarget']

/-- A phase-zero drain acquire observes the actual second query return notification. -/
private theorem secondQueryReturnObserved {wait : EvId} {e : Event} (he : X.get wait = some e)
    (hk : e.kind = .wait (secondQueryEmpty l (wait.1 / l.block)) 0 true true .cta) :
    ∃ (issue : EvId) (spec : TcCommit.Spec) (rank : Fin 16),
      X.get issue = some ⟨(Mma.commitSite (Mma.queryReleaseSite 1)).pc, .tc (.commit spec)⟩ ∧
      issue.1 / l.block = wait.1 / l.block ∧
      TcCommit.target spec rank = some (secondQueryEmpty l (wait.1 / l.block)) ∧
      MbarObserved X (.async issue (.tcNotify rank)) (.thread wait) := by
  classical
  obtain ⟨site, e⟩ := e
  change e = _ at hk
  subst e
  let loc := secondQueryEmpty l (wait.1 / l.block)
  let log := X.objects loc
  obtain ⟨j, poll, hPoll, hId, hAction, _, hSuccess⟩ := actualPollRecordClean hp hX he
  have hInit : PairTmaRing.InitFirst X loc 1 :=
    (activeObjectHistory hp hX (3 : Fin 34) (List.mem_of_getElem? hPoll)).1
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hUpdate {r : Record Ref} (hr : r ∈ log) (h : CounterUpdate r.action) :=
    queryEmptyUpdateAt hp hX 1 hr h
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr h
    obtain ⟨_, _, _, _, _, _, _, _, ha⟩ := hUpdate hr (by rw [h]; trivial)
    rw [h] at ha
    cases ha
  obtain ⟨st, q, hState, hPollAct, hParity, hCompleted⟩ := hChecked.okPoll hPoll hSuccess
  have hq := (Action.pollParity.inj (hAction.symm.trans hPollAct)).1.symm
  subst q
  have hPositive : 0 < st.phase := by omega
  have hSeen : observedAt log j = some (st.phase-1) := by
    change log[j]? = some poll at hPoll
    simp only [observedAt, hPoll, Option.bind_some, hCompleted, ite_eq_left hPositive]
  have hCard := hChecked.card_unit_arrivals_phase hNo (n := 1) (q := st.phase-1)
    (fun _ r count tx hr _ ha => by
      obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hUpdate (List.mem_of_getElem? hr) (by rw [ha]; trivial)
      rw [ha] at h
      exact (Action.arrive.inj h).1)
    (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNo h) hIncr
    (List.getElem?_eq_some_iff.mp hPoll).1.le hState (by omega)
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < _ from hCard.symm ▸ Nat.zero_lt_one)
  obtain ⟨_, r, tx, hr, ha, hf, hAt⟩ := Finset.mem_filter.mp hk
  obtain ⟨g, index, rank, spec, hRid, hCommit, hCta, hTarget, _⟩ :=
    hUpdate (List.mem_of_getElem? hr) (by rw [ha]; trivial)
  have hObs := hX.observed_of_phase hNo hr hf (by rw [ha]; trivial) hPoll hSuccess hAt hSeen
  rw [hRid, hId] at hObs
  exact ⟨(g,index), spec, rank, hCommit, hCta, hTarget, hObs⟩

/-- The successful second query drain acquire identifies an actual return notification. -/
theorem secondQueryEmptyObserver {wait : EvId} {e : Event} (he : X.get wait = some e)
    (hk : e.kind = .wait (secondQueryEmpty l (wait.1 / l.block)) 0 true true .cta) :
    ∃ issue spec rank, X.Commit issue spec ∧ issue.1 / l.block = wait.1 / l.block ∧
      TcCommit.target spec rank = some (secondQueryEmpty l (wait.1 / l.block)) ∧
      MbarObserved X (.async issue (.tcNotify rank)) (.thread wait) := by
  obtain ⟨issue, spec, rank, hCommit, hCta, hTarget, hObs⟩ :=
    secondQueryReturnObserved hp hX he hk
  exact ⟨issue, spec, rank, ⟨_, hCommit⟩, hCta, hTarget, hObs⟩

/-- A loader that observes completion of the second query's empty object depends on the MMA
acquire of the corresponding query input. -/
theorem secondQueryAcquireBeforeEmptyWait {wait : EvId} {e : Event} (he : X.get wait = some e)
    (hk : e.kind = .wait (secondQueryEmpty l (wait.1 / l.block)) 0 true true .cta) :
    ∃ acquire f, acquire.1 / l.block = wait.1 / l.block ∧ X.get acquire = some f ∧
      f.kind = .wait (queryObject l (wait.1 / l.block) 1) 0 true true .cta ∧
      Relation.TransGen (DepStep l kernel X) (.thread acquire,true) (.thread wait,true) := by
  obtain ⟨⟨g,index⟩, spec, rank, hCommit, hCta, _, hObs⟩ :=
    secondQueryReturnObserved hp hX he hk
  have hPresent : X.AsyncPresent (g,index) (.tcNotify rank) := hObs.1
  obtain ⟨waitIndex, _, target, p, hQuery, hResumes⟩ :=
    Mma.secondQueryWaitBeforeDrain hp hX hCommit
  obtain ⟨hTarget, rfl⟩ := Mma.secondQueryPollOperands hp hX hQuery
  change g / l.block = wait.1 / l.block at hCta
  rw [hCta] at hTarget
  have hPath : Relation.TransGen (DepStep l kernel X) (.thread (g,waitIndex),true)
      (.async (g,index) (.tcNotify rank),false) :=
    (Relation.TransGen.single (DepStep.of_resumes (L := l) hResumes)).tail
    (DepStep.issue ⟨_, hCommit⟩ hPresent
      (by intro t h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h))
  exact ⟨(g,waitIndex), _, hCta, hQuery,
    congrArg (fun loc => Kind.wait loc 0 true true .cta) hTarget,
    hPath.tail (DepStep.of_witness (L := l) (Witness.of_mbarObserved hObs))⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

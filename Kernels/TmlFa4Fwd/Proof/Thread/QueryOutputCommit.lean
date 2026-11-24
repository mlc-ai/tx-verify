-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStaging
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondOutputAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryInputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryReleaseOnce
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.MmaRingAddress
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
public import Kernels.TmlFa4Fwd.Proof.MmaFirstQueryOperand
public import Lemmas.Protocol.PairTmaRing.Hyp
import Lemmas.Protocol.MbarRingRound
import Lemmas.Execution.ExecutionGrowth
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.MBarrier PTX.AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Loader
open PTX.Kernels.TmlFa4Fwd.Thread.Correction (FirstOutputAcquire SecondOutputAcquire)
open PTX.Kernels.TmlFa4Fwd.Mma (mmaFixedCommitExactAddress fixedMmaCommitOffset
  mmaRingCommitAddress)
open PTX.Kernels.TmlFa4Fwd.Mma
  (firstQueryOperandFragmentBeforeOutputCommitOfPrefix QueryOperandFragment)
open PTX.Kernels.TmlFa4Fwd.Mma (firstQueryWaitBeforeGate firstQueryPollOperands)

noncomputable section

def firstOutputObject (l : Launch) (cta : Nat) : Loc :=
  ⟨.shared, cta, l.sharedBase + 144⟩

/-- The terminal Tensor Core commit that makes the first MMA output stage available. -/
def FirstOutputCommit (X : Execution) (commit : EvId) (s : TcCommit.Spec) : Prop :=
  X.get commit = some ⟨2642, .tc (.commit s)⟩

theorem FirstOutputCommit.issued {X : Execution} {commit : EvId} {s : TcCommit.Spec}
    (h : FirstOutputCommit X commit s) : X.Commit commit s := ⟨_, h⟩

private def outputCompletionPc (stage : Fin 2) : Nat :=
  if stage = 0 then 2642 else 2646

/-- The CTA-local object notified when the last MMA for an output stage completes. -/
def outputCompletionObject (l : Launch) (cta : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + (144 + 8 * stage.val)⟩

/-- The second MMA output stage has its own completion object. -/
def secondOutputObject (l : Launch) (cta : Nat) : Loc :=
  ⟨.shared, cta, l.sharedBase + 152⟩

/-- The terminal Tensor Core commit that makes the second MMA output stage available. -/
@[no_expose] def SecondOutputCommit (X : Execution) (commit : EvId) (s : TcCommit.Spec) : Prop :=
  X.get commit = some ⟨2646, .tc (.commit s)⟩

/-- Recover the stage-one commit site within the Thread proofs. -/
theorem SecondOutputCommit.decoded {X : Execution} {commit : EvId} {s : TcCommit.Spec}
    (h : SecondOutputCommit X commit s) :
    X.get commit = some ⟨2646, .tc (.commit s)⟩ := h

/-- An execution extension preserves an observed terminal output commit. -/
theorem SecondOutputCommit.mono {X Y : Execution} {commit : EvId} {s : TcCommit.Spec}
    (h : SecondOutputCommit X commit s) (hPrefix : X.le Y) :
    SecondOutputCommit Y commit s :=
  Execution.le_get hPrefix h.decoded

/-- The stage-one completion comes from an actual Tensor Core commit. -/
theorem SecondOutputCommit.issued {X : Execution} {commit : EvId} {s : TcCommit.Spec}
    (h : SecondOutputCommit X commit s) : X.Commit commit s := ⟨_, h⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem outputCommitSite (stage : Fin 2) {commit : EvId} {pos cta : Nat} {s : TcCommit.Spec}
    {rank : Fin 16} (he : X.get commit = some ⟨pos, .tc (.commit s)⟩)
    (ht : TcCommit.target s rank = some (outputCompletionObject l cta stage)) :
    pos = outputCompletionPc stage ∧ commit.1 / l.block = cta := by
  rcases inCommitSites hX he with hf | hr
  · have hLoc := mmaFixedCommitExactAddress hp hX he hf ht
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (144 + 8 * stage.val) = l.sharedBase + fixedMmaCommitOffset pos at hAddr
    have hOff := Nat.add_left_cancel hAddr
    simp only [fixedCommits, List.mem_cons, List.not_mem_nil, or_false] at hf
    have hSite : pos = outputCompletionPc stage := by
      fin_cases stage <;> rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | (simp [fixedMmaCommitOffset] at hOff)
    exact ⟨hSite, (congrArg Loc.cta hLoc).symm⟩
  · obtain ⟨slot, hLoc⟩ := mmaRingCommitAddress hp hX he hr ht
    have hAddr := congrArg Loc.addr hLoc
    change l.sharedBase + (144 + 8 * stage.val) = l.sharedBase + (8 * slot.val + 56) at hAddr
    have := slot.isLt
    omega

/-- An actual commit targeting output completion is one of the two terminal notifications. -/
theorem outputCommitOfTarget (stage : Fin 2) {i : EvId} {cta : Nat} {spec : TcCommit.Spec}
    {rank : Fin 16} (hi : X.Commit i spec)
    (ht : TcCommit.target spec rank = some (outputCompletionObject l cta stage)) :
    FirstOutputCommit X i spec ∨ SecondOutputCommit X i spec := by
  obtain ⟨_, he⟩ := hi
  have hs := (outputCommitSite hp hX stage he ht).1
  rw [hs] at he
  fin_cases stage
  · exact .inl he
  · exact .inr he

private theorem outputNotAsyncArrive (stage : Fin 2) {cta : Nat} {i : EvId} {noinc : Bool}
    (h : X.AsyncArrive i (outputCompletionObject l cta stage) noinc) : False := by
  obtain ⟨pos, he⟩ := h
  obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := actualAsyncArrival hX he
  have hSite : copyCommitPc site + 1 ∈ [674, 904, 1137, 1342, 1602, 1735] := by
    fin_cases site <;> decide
  obtain ⟨off, hOff, hLoc⟩ := loaderAsyncAddress hp hX he hSite
  have hAddr : l.sharedBase + (144 + 8 * stage.val) = l.sharedBase + off :=
    congrArg Loc.addr hLoc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  omega

private theorem outputUpdateAt (stage : Fin 2) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (outputCompletionObject l cta stage)) (hUpdate : CounterUpdate r.action) :
    ∃ commit s rank, r.id = .async commit (.tcNotify rank) ∧
      X.get commit = some ⟨outputCompletionPc stage, .tc (.commit s)⟩ ∧ commit.1 / l.block = cta ∧
      TcCommit.target s rank = some (outputCompletionObject l cta stage) ∧
      r.action = .arrive 1 0 := by
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha | wait _ _ ha | inval _ _ ha => rw [ha] at hUpdate; exact hUpdate.elim
  | arrive _ he _ =>
    obtain ⟨off, hOff, hLoc⟩ := actualArriveOffsetIn hp hX he
    have hAddr : l.sharedBase + (144 + 8 * stage.val) = l.sharedBase + off :=
      congrArg Loc.addr hLoc
    obtain rfl : off = 144 + 8 * stage.val := by omega
    exact ((show 144 + 8 * stage.val ∉ ordinaryArriveOffsets by
      fin_cases stage <;> decide) hOff).elim
  | increment _ he _ => exact (noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor _ he hTarget _ =>
    obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
    have hLoc := loaderTensorOffset hp hX site he
    have audit : ∀ (j : Fin 14) (s : Fin 2),
        inputBarrierBase j + (inputSite j).barrierOffset ≠ 144 + 8 * s.val := by decide
    have hAddr := congrArg Loc.addr (hTarget.symm.trans hLoc)
    change l.sharedBase + (144 + 8 * stage.val) =
      l.sharedBase + (inputBarrierBase site + (inputSite site).barrierOffset) at hAddr
    exact (audit site stage (by omega)).elim
  | arriveOn _ he hm _ _ =>
    exact (outputNotAsyncArrive hp hX stage ⟨_, by simpa only [hm] using he⟩).elim
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit hId he ht ha =>
    have ⟨hSite, hCta⟩ := outputCommitSite hp hX stage he ht
    exact ⟨_, _, _, hId, hSite ▸ he, hCta, ht, ha⟩
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

/-- Every actual MMA output-completion update is a unit notification with no expected bytes. -/
theorem outputCompletionUpdate (stage : Fin 2) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (outputCompletionObject l cta stage)) (hUpdate : CounterUpdate r.action)
    : r.action = .arrive 1 0 := by
  obtain ⟨_, _, _, _, _, _, _, hAct⟩ := outputUpdateAt hp hX stage hr hUpdate
  exact hAct

/-- There is at most one actual MMA output notification per CTA and stage. -/
theorem outputCompletionUpdateUnique (stage : Fin 2) {cta : Nat} {r q : Record Ref}
    (hr : r ∈ X.objects (outputCompletionObject l cta stage))
    (hq : q ∈ X.objects (outputCompletionObject l cta stage)) (hR : CounterUpdate r.action)
    (hQ : CounterUpdate q.action) : r.id = q.id := by
  obtain ⟨i, a, x, hId, hi, hCta, hTarget, _⟩ := outputUpdateAt hp hX stage hr hR
  obtain ⟨j, b, y, hId', hj, hCta', hTarget', _⟩ := outputUpdateAt hp hX stage hq hQ
  have hSite : (Mma.TerminalCommit.output stage).pc = outputCompletionPc stage := by
    fin_cases stage <;> rfl
  have hEv := Mma.terminalCommitUnique hp hX (.output stage) (hCta.trans hCta'.symm)
    (hSite.symm ▸ hi) (hSite.symm ▸ hj)
  subst j
  rw [hi] at hj
  have hSpec := TcKind.commit.inj (Kind.tc.inj (Event.mk.inj (Option.some.inj hj)).2)
  subst b
  rw [hId, hId', MbarRing.Notify.rank_eq hTarget hTarget']

/-- MMA output notifications and polls use the initialized single-credit stage object. -/
theorem outputCompletionInitialized (stage : Fin 2) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (outputCompletionObject l cta stage)) :
    PairTmaRing.InitFirst X (outputCompletionObject l cta stage) 1 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (18 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (19 : Fin 34) hr).1

private theorem outputAcquireCommitOfEvent (stage : Fin 2) {wait : EvId} {pos : Nat}
    {scope : MbarScope}
    (he : X.get wait = some ⟨pos,
      .wait (outputCompletionObject l (wait.1 / l.block) stage) 0 true true scope⟩) :
    ∃ commit s rank, X.get commit = some ⟨outputCompletionPc stage, .tc (.commit s)⟩ ∧
      SameCta l commit.1 wait.1 ∧ TcCommit.target s rank =
        some (outputCompletionObject l (wait.1 / l.block) stage) ∧
      rank ∈ X.tcNotified commit ∧
      WaitObserves X (.async commit (.tcNotify rank)) wait
        (outputCompletionObject l (wait.1 / l.block) stage) true scope := by
  let loc := outputCompletionObject l (wait.1 / l.block) stage
  let log := X.objects loc
  obtain ⟨j, poll, hj, hId, ha, hClean, hSuccess⟩ := actualPollRecordClean hp hX he
  have hChecked := X.objects_checked hX loc
  obtain ⟨st, n, hSt, ha', hParity, hFinished⟩ := hChecked.okPoll hj hSuccess
  obtain rfl : n = 0 := (Action.pollParity.inj (ha'.symm.trans ha)).1
  have hPos : 0 < st.phase := by omega
  let phase := st.phase - 1
  have hObserved : observedAt log j = some phase := by
    change (log[j]?).bind (fun r => r.reply.completed) = some phase
    change log[j]? = some poll at hj
    rw [hj, Option.bind_some, hFinished, ite_eq_left hPos]
  have hNo := objects_noInval hX.tma.2.2.1 (fun e _ => noMbarInval hX (i := e)) loc
  have hLen : j < log.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨q, hq, hCompletion⟩ := hChecked.crossing hNo hLen.le hSt
    (show phase < st.phase by dsimp [phase]; omega)
  have hUnits := (hChecked.completion_sums hNo (hq.trans hLen) hCompletion).2
  obtain ⟨index, hIndex, hNonzero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hUnits)
  have hCredited : phaseAt log index = some phase ∧ unitsAt log index ≠ 0 := by
    simpa [log, apply_ite] using hNonzero
  obtain ⟨hPhase, hUnits'⟩ := hCredited
  obtain ⟨rec, hr⟩ : ∃ rec, log[index]? = some rec := by
    cases hGet : log[index]? with
    | none => simp [unitsAt, hGet] at hUnits'
    | some rec => exact ⟨rec, rfl⟩
  have hR : rec.fault = none ∧ rec.action.units ≠ 0 := by
    simpa [unitsAt, hr] using hUnits'
  have hUpdate : CounterUpdate rec.action := by
    cases ha : rec.action <;> simp [ha, Action.units, CounterUpdate] at hR ⊢
  obtain ⟨commit, s, rank, hNote, hc, hCta, ht, _⟩ :=
    outputUpdateAt hp hX stage (List.mem_of_getElem? hr) hUpdate
  have hBefore := MbarRing.Slot.updateBeforeWait_of_phase hChecked hNo hr hR.1 hj hClean hSuccess
    hPhase hObserved
  rw [hNote, hId] at hBefore
  have hDelivered : rank ∈ X.tcNotified commit := by
    by_contra hBad
    exact (no_tc_notification_record hX.tma.2.2.1 hBad (List.mem_of_getElem? hr)) hNote
  exact ⟨commit, s, rank, hc,
    ⟨event_thread_lt hX hc, event_thread_lt hX he, hCta⟩, ht, hDelivered,
    ⟨⟨pos, 0, he⟩, hBefore⟩⟩

/-- The first correction output acquire observes an actual final MMA commit in its own CTA. -/
theorem firstOutputAcquireCommit {wait : EvId} (hWait : FirstOutputAcquire l X wait) :
    ∃ commit s rank scope, FirstOutputCommit X commit s ∧
      SameCta l commit.1 wait.1 ∧ TcCommit.target s rank =
        some (firstOutputObject l (wait.1 / l.block)) ∧
      rank ∈ X.tcNotified commit ∧
      WaitObserves X (.async commit (.tcNotify rank)) wait
        (firstOutputObject l (wait.1 / l.block)) true scope := by
  obtain ⟨⟨pos, kind⟩, scope, he, hk⟩ := hWait
  change kind = _ at hk
  subst kind
  obtain ⟨commit, s, rank, hIssued, hCta, hTarget, hDelivered, hObserve⟩ :=
    outputAcquireCommitOfEvent hp hX 0 he
  exact ⟨commit, s, rank, scope, hIssued, hCta, hTarget, hDelivered, hObserve⟩

/-- The second correction output acquire observes an actual final MMA commit in its own CTA. -/
theorem secondOutputAcquireCommit {wait : EvId} (hWait : SecondOutputAcquire l X wait) :
    ∃ commit s rank scope, SecondOutputCommit X commit s ∧
      SameCta l commit.1 wait.1 ∧ TcCommit.target s rank =
        some (secondOutputObject l (wait.1 / l.block)) ∧
      rank ∈ X.tcNotified commit ∧
      WaitObserves X (.async commit (.tcNotify rank)) wait
        (secondOutputObject l (wait.1 / l.block)) true scope := by
  obtain ⟨⟨pos, kind⟩, scope, he, hk⟩ := hWait
  change kind = _ at hk
  subst kind
  obtain ⟨commit, s, rank, hIssued, hCta, hTarget, hDelivered, hObserve⟩ :=
    outputAcquireCommitOfEvent hp hX 1 he
  exact ⟨commit, s, rank, scope, hIssued, hCta, hTarget, hDelivered, hObserve⟩

omit hp hX in
private theorem trackedOutputAcquireRead {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {commit wait : EvId} {s : TcCommit.Spec}
    {rank : Fin 16} {scope : MbarScope} {object : Loc} (hc : X.Commit commit s)
    (hCta : SameCta l commit.1 wait.1) (hTarget : TcCommit.target s rank = some object)
    (hNotified : rank ∈ X.tcNotified commit)
    (hObserve : WaitObserves X (.async commit (.tcNotify rank)) wait object true scope)
    {mma : EvId} {d index : Nat} {op : TcMma.OperandSpec}
    {isB accum : Bool} {mask : List Nat} {loc : Loc}
    (hIssue : X.MmaIssue mma d op accum mask) (hLane : mma.1 = commit.1)
    (hEarlier : mma.2 < commit.2)
    (hByte : op.byteLoc (if isB then .b else .a) index = some loc) :
    AsyncObserved X mma .mmaDone wait true scope ∧
      ScopesMeet l .cluster mma.1 scope wait.1 ∧
      ∃ value, X.MmaRead mma isB index loc value := by
  have hTrack : TracksMma X mma commit :=
    ⟨hLane, hEarlier, .inl ⟨d, op, accum, mask, hIssue⟩, s, hc⟩
  have hSeen : AsyncObserved X mma .mmaDone wait true scope :=
    ⟨.async commit (.tcNotify rank), _, ⟨commit, s, rank, rfl, hTrack, hc, hTarget,
      hNotified⟩, hObserve⟩
  have hDone := (hX.tcCommit commit rank hNotified).2 mma hTrack
  obtain ⟨operands, hOperands⟩ := Option.isSome_iff_exists.mp (hX.tma.2.1.2 mma hDone)
  obtain ⟨value, hRead, _⟩ := hX.tma.2.1.mma_read_exists hIssue hOperands hByte
  exact ⟨hSeen, MbarRing.Unit.Gate.scopesMeet (hLane.symm ▸ hCta) .cluster scope, value, hRead⟩

/-- The first output acquire observes the completion and actual operand byte of an MMA
tracked by its terminal commit. -/
theorem firstOutputAcquireReads {wait : EvId} (hWait : FirstOutputAcquire l X wait) :
    ∃ commit s scope, FirstOutputCommit X commit s ∧ SameCta l commit.1 wait.1 ∧
      ∀ {mma : EvId} {d index : Nat} {op : TcMma.OperandSpec}
        {isB accum : Bool} {mask : List Nat} {loc : Loc},
        X.MmaIssue mma d op accum mask → mma.1 = commit.1 → mma.2 < commit.2 →
        op.byteLoc (if isB then .b else .a) index = some loc →
        AsyncObserved X mma .mmaDone wait true scope ∧
        ScopesMeet l .cluster mma.1 scope wait.1 ∧
        ∃ value, X.MmaRead mma isB index loc value := by
  obtain ⟨commit, s, rank, scope, hc, hCta, hTarget, hNotified, hObserve⟩ :=
    firstOutputAcquireCommit hp hX hWait
  exact ⟨commit, s, scope, hc, hCta,
    trackedOutputAcquireRead hX hc.issued hCta hTarget hNotified hObserve⟩

/-- The second output acquire observes the completion and actual operand byte of an MMA
tracked by its terminal commit. -/
theorem secondOutputAcquireReads {wait : EvId} (hWait : SecondOutputAcquire l X wait) :
    ∃ commit s scope, SecondOutputCommit X commit s ∧ SameCta l commit.1 wait.1 ∧
      ∀ {mma : EvId} {d index : Nat} {op : TcMma.OperandSpec}
        {isB accum : Bool} {mask : List Nat} {loc : Loc},
        X.MmaIssue mma d op accum mask → mma.1 = commit.1 → mma.2 < commit.2 →
        op.byteLoc (if isB then .b else .a) index = some loc →
        AsyncObserved X mma .mmaDone wait true scope ∧
        ScopesMeet l .cluster mma.1 scope wait.1 ∧
        ∃ value, X.MmaRead mma isB index loc value := by
  obtain ⟨commit, s, rank, scope, hc, hCta, hTarget, hNotified, hObserve⟩ :=
    secondOutputAcquireCommit hp hX hWait
  exact ⟨commit, s, scope, hc, hCta,
    trackedOutputAcquireRead hX hc.issued hCta hTarget hNotified hObserve⟩

/-- An actual output commit tracks a QK issue on its elected lane. The issue follows the
lane's successful initial Q0 acquire and uses the first Q0 descriptor. -/
theorem firstOutputCommitHasQueryFragmentOfPrefix {commit : EvId} {spec : TcCommit.Spec}
    (he : FirstOutputCommit X commit spec) :
    ∃ mma wait e d op accum mask,
      mma.1 = commit.1 ∧ mma.2 < commit.2 ∧ X.MmaIssue mma d op accum mask ∧
      X.get wait = some e ∧ e.kind = .wait (Output.queryObject l (mma.1 / l.block) 0)
        0 true true .cta ∧ TraceBefore X wait mma ∧
      QueryOperandFragment l mma.1 0 0 op ∧
      ∀ byte < 4, op.byteLoc .a byte = some ⟨.shared, mma.1 / l.block,
        l.sharedBase + 3072 + byte⟩ := by
  obtain ⟨g, index⟩ := commit
  obtain ⟨j, hj, d, op, accum, mask, hIssue, hOperand, hAddr⟩ :=
    firstQueryOperandFragmentBeforeOutputCommitOfPrefix hp hX he
  obtain ⟨i, hi, bar, phase, hWait, _⟩ := firstQueryWaitBeforeGate hp hX hIssue
    (show 2145 ≤ 2197 by decide) (show 2197 ≤ 2642 by decide)
  obtain ⟨rfl, rfl⟩ := firstQueryPollOperands hp hX hWait
  exact ⟨(g, j), (g, i), _, d, op, accum, mask, rfl, hj, ⟨_, hIssue⟩, hWait, rfl,
    ⟨rfl, hi, (List.getElem?_eq_some_iff.mp hIssue).1⟩, hOperand, hAddr⟩

/-- An actual output commit tracks a QK issue on its elected lane. The issue follows the
lane's successful initial Q0 acquire and reads the first four bytes of the Q0 stage. -/
theorem firstOutputCommitHasQueryBytesOfPrefix {commit : EvId} {spec : TcCommit.Spec}
    (he : FirstOutputCommit X commit spec) :
    ∃ mma wait e d op accum mask,
      mma.1 = commit.1 ∧ mma.2 < commit.2 ∧ X.MmaIssue mma d op accum mask ∧
      X.get wait = some e ∧ e.kind = .wait (Output.queryObject l (mma.1 / l.block) 0)
        0 true true .cta ∧ TraceBefore X wait mma ∧
      ∀ byte < 4, op.byteLoc .a byte = some ⟨.shared, mma.1 / l.block,
        l.sharedBase + 3072 + byte⟩ := by
  obtain ⟨mma, wait, e, d, op, accum, mask, hLane, hBefore, hMma, hPoll, hKind, hTrace, _, hRead⟩ :=
    firstOutputCommitHasQueryFragmentOfPrefix hp hX he
  exact ⟨mma, wait, e, d, op, accum, mask, hLane, hBefore, hMma, hPoll, hKind, hTrace, hRead⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread

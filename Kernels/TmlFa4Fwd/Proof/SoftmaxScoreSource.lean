-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkCommit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreTrace
public import Lemmas.Execution.NoTcCp
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotTcShift
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Protocol.UnitGate
public import Lemmas.Tcgen05.TcCommit
public import Lemmas.Tcgen05.TcNotifyObject
public import Lemmas.Tcgen05.TmemWriters

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.Flow

/-- The two initial QK blocks are the first use of the two softmax stages. -/
def firstQkBlock (stage : Fin 2) : Fin 4 :=
  ⟨stage.val, by have := stage.isLt; omega⟩

@[simp] theorem firstQkBlock_stage (stage : Fin 2) : Mma.qkStage (firstQkBlock stage) = stage := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt stage.isLt

/-- The producer's commit and the consumer's successful poll belong to the same completed
QK-full phase. This records the physical object and the particular wait and delivery. -/
structure FirstQkPhase (l : Launch) (X : Execution) (stage : Fin 2)
    (producer consumer commit wait : Nat) : Prop where
  sameCta : SameCta l producer consumer
  commitEvent : X.get (producer, commit) =
    some ⟨(Mma.commitSite (Mma.qkCommitSite (firstQkBlock stage))).pc,
      .tc (.commit (Mma.commitSpec l producer (waitLoc l consumer stage 1).addr))⟩
  waitEvent : X.get (consumer, wait) =
    some ⟨3425, .wait (waitLoc l consumer stage 1) 0 true true .cta⟩
  observed : MBarrier.UpdateBeforeWait (X.objects (waitLoc l consumer stage 1))
    (.async (producer, commit) (.tcNotify 0)) (.thread (consumer, wait))

/-- The successful wait's ordinal comes from the observed retry prefix of the same thread. -/
theorem firstScoreSuccessfulWait {l : Launch} {X : Execution} (stage : Fin 2)
    {g j fails : Nat}
    (hPolls : (X.tr g).drop j =
      List.replicate fails ⟨3425, .wait (waitLoc l g stage 1) 0 false true .cta⟩ ++
        ⟨3425, .wait (waitLoc l g stage 1) 0 true true .cta⟩ ::
          (X.tr g).drop (j+fails+1)) :
    X.get (g, j+fails) = some ⟨3425, .wait (waitLoc l g stage 1) 0 true true .cta⟩ := by
  change (X.tr g)[j+fails]? = _
  rw [← List.getElem?_drop, hPolls, List.getElem?_append_right (by simp)]
  simp

variable {l : Launch} {m : Mem0} {X : Execution}

/-- The actual initial acquire observes each MMA issue tracked by its score commit. -/
theorem firstQkPhase_observed (hX : Consistent l kernel Assumptions.all m X) {stage : Fin 2}
    {producer consumer issue commit wait : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    (hi : X.TcAsync (producer, issue)) (hBefore : issue < commit) :
    AsyncCopy.AsyncObserved X (producer, issue) .mmaDone (consumer, wait) true .cta := by
  let mb := waitLoc l consumer stage 1
  let spec := Mma.commitSpec l producer mb.addr
  have hSpec : spec = TcCommit.unicast mb := by
    simp only [spec, Mma.commitSpec, TcCommit.unicast, mb, waitLoc, hPhase.sameCta.2.2]
  have hCommit : X.Commit (producer, commit) spec :=
    ⟨_, hPhase.commitEvent⟩
  have hTrack : AsyncCopy.TracksMma X (producer, issue) (producer, commit) :=
    ⟨rfl, hBefore, hi, ⟨spec, hCommit⟩⟩
  have hTarget : TcCommit.target spec 0 = some mb := by
    rw [hSpec]
    exact TcCommit.target_unicast rfl
  have hDelivered : (0 : Fin 16) ∈ X.tcNotified (producer, commit) := by
    obtain ⟨_, _, r, _, _, hr, hid, _, _, _, _, _, _, _, _⟩ := hPhase.observed
    by_contra hNo
    exact (no_tc_notification_record hX.tma.2.2.1 hNo (List.mem_of_getElem? hr)) hid
  exact ⟨.async (producer, commit) (.tcNotify 0), mb,
    ⟨(producer, commit), spec, 0, rfl, hTrack, hCommit, hTarget, hDelivered⟩,
    ⟨⟨3425, 0, hPhase.waitEvent⟩, hPhase.observed⟩⟩

/-- The commit tracks the last QK issue, and its actual acquire wait orders it before each
of the four first-round score loads in the receiving thread. -/
theorem firstScoreDoneBefore (hX : Consistent l kernel Assumptions.all m X) {stage : Fin 2}
    {producer consumer issue commit wait read : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    (hi : X.TcAsync (producer, issue)) (hBefore : issue < commit) (q : Fin 4) {vals : List Value}
    (he : X.get (consumer, read) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hAfter : wait < read) : DoneBefore l X (producer, issue) (consumer, read) := by
  have hLen : read < (X.tr consumer).length := (List.getElem?_eq_some_iff.mp he).1
  have hProgram : po X (consumer, wait) (consumer, read) :=
    po_of_not_access rfl hAfter hLen (by rw [he]; rfl)
  exact .inl ⟨(consumer, wait), .cta, firstQkPhase_observed hX hPhase hi hBefore,
    PTX.MbarRing.Unit.Gate.scopesMeet hPhase.sameCta .cluster .cta, .single (.inl hProgram)⟩

/-- The same-PC wait before the first probability store also precedes every later probability
store issued by this lane. -/
theorem firstScoresBeforeLocalStore {l : Launch} {X : Execution} {g read complete write : Nat}
    (hComplete : X.get (g, complete) = some ⟨4826, .tc .waitLd⟩) (hRead : read < complete)
    {addr : Nat} {vals : List Value} {shape : TcShape}
    (hStore : X.TSt (g, write) addr vals shape) (hWrite : complete < write) :
    ReadBefore l X .ld (g, read) (g, write) := by
  obtain ⟨_, he⟩ := hStore
  have hLen : write < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hp : po X (g, complete) (g, write) :=
    po_of_not_access rfl hWrite hLen (by rw [he]; rfl)
  exact ReadBefore.of_waitLd hComplete rfl hRead (.inl (.single (.inl hp)))

private theorem scoreResultWrite {L : Launch} {A : List Assumption} {X : Execution}
    {issue : EvId} {cell : Cell} {v : Value} (hr : Result L A X issue cell v) :
    X.MmaCell issue cell := by
  cases hr with
  | overwrite hi hp _ _ => exact ⟨_, _, _, _, _, _, hi, hp⟩
  | accumulate hi hp _ _ _ _ => exact ⟨_, _, _, _, _, _, hi, hp⟩
  | accumulateStored hi hp _ _ _ _ => exact ⟨_, _, _, _, _, _, hi, hp⟩

/-- A score read takes the committed QK result once all other writes to its exact cell
are outside the source-to-read interval and the allocation remains live. -/
theorem firstScoreReadSource (hX : Consistent l kernel Assumptions.all m X) {stage : Fin 2}
    {producer consumer issue commit wait read : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait) (hBefore : issue < commit)
    (q : Fin 4) (word : Fin 32) {vals : List Value} {v : Value}
    (he : X.get (consumer, read) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hAfter : wait < read)
    (hResult : Result l Assumptions.all X (producer, issue)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val) v)
    (hOther : ∀ other, TmemWrite l X other
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val) →
      other = (producer, issue) ∨ WriteBefore l X other (producer, issue) ∨
        ReadBefore l X .ld (consumer, read) other)
    (hLive : SourceLive l X (producer, issue) (consumer, read)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    ReadSource l X .ld (producer, issue) (consumer, read)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val) := by
  have hAsync : X.TcAsync (producer, issue) := .inl hResult.mmaIssue
  have hSource : (producer, issue) ≠ (consumer, read) := by
    intro hEq
    obtain ⟨d, spec, acc, mask, pc, hf⟩ := hResult.mmaIssue
    rw [hEq, he] at hf
    cases hf
  exact ⟨hSource, .inl (scoreResultWrite hResult),
    WriteBefore.of_done (firstScoreDoneBefore hX hPhase hAsync hBefore q he hAfter), hOther, hLive⟩

private theorem noScoreCopyCode : kernel.NoTcCp = true := by
  decide +kernel

private theorem noScoreShiftCode : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- Tensor Memory cells can be written only by an MMA result or a store in this kernel. -/
theorem scoreWriteCases (hX : Consistent l kernel Assumptions.all m X) {writer : EvId} {cell : Cell}
    (hWrite : TmemWrite l X writer cell) :
    X.MmaCell writer cell ∨ StoreCell l X writer cell := by
  have hNoShift : ∀ i s, ¬ X.ShiftIssue i s := by
    rintro i s ⟨pc, hGet⟩
    exact no_kind_of_code hX tcShiftOp (fun k => ∃ spec, k = .tc (.shift spec))
      (fun _ ⟨_, h⟩ => by cases h)
      (fun hF ⟨_, h⟩ => fires_tcShift_op hF h) noScoreShiftCode hGet ⟨s, rfl⟩
  exact tmemWrite_of_no_copy (noCp_of_consistent noScoreCopyCode hX) hNoShift hWrite

private theorem firstQkFragmentsPipe {l : Launch} {X : Execution} {g start use : Nat}
    (hg : g < l.threads) (stage : Fin 2)
    (hIssues : ∀ step : Fin 8, X.get (g, start+step.val) =
      some (Mma.qkIssueEvent l g (firstQkBlock stage) step use))
    {a b : Fin 8} (hlt : a.val < b.val) :
    Pipelined l X .dWrite (g, start+a.val) .dWrite (g, start+b.val) := by
  let block := firstQkBlock stage
  have hLen : start+b.val < (X.tr g).length := (List.getElem?_eq_some_iff.mp (hIssues b)).1
  have hOrder : po X (g, start+a.val) (g, start+b.val) :=
    po_of_not_access rfl (by omega) hLen (by rw [hIssues b]; rfl)
  exact ⟨⟨⟨hg, hg, rfl⟩, rfl⟩, .inl (.single (.inl hOrder)),
    scoreColumn (Mma.qkStage block), Mma.qkOperands l g block a use, _, _,
    scoreColumn (Mma.qkStage block), Mma.qkOperands l g block b use, _, _,
    ⟨_, hIssues a⟩, ⟨_, hIssues b⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The issued fragments of the same QK block update the same accumulator in issue order. -/
theorem firstQkFragmentsBefore {l : Launch} {X : Execution} {g start use : Nat}
    (hg : g < l.threads) (stage : Fin 2)
    (hIssues : ∀ step : Fin 8, X.get (g, start+step.val) =
      some (Mma.qkIssueEvent l g (firstQkBlock stage) step use))
    {a b : Fin 8} (hlt : a.val < b.val) :
    WriteBefore l X (g, start+a.val) (g, start+b.val) :=
  .inl (.inr (firstQkFragmentsPipe hg stage hIssues hlt))

/-- Only MMA or store writes outside the initially committed block need a separate
inter-round ordering argument. The earlier fragments in that block are ordered by issue. -/
theorem firstQkOtherWrites (hX : Consistent l kernel Assumptions.all m X) {producer start use : Nat}
    (hg : producer < l.threads) (stage : Fin 2)
    (hIssues : ∀ step : Fin 8, X.get (producer, start+step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step use)) (read : EvId) (cell : Cell)
    (hOutside : ∀ other, (X.MmaCell other cell ∨ StoreCell l X other cell) →
      (∀ step : Fin 8, other ≠ (producer, start+step.val)) →
      WriteBefore l X other (producer, start+7) ∨ ReadBefore l X .ld read other) :
    ∀ other, TmemWrite l X other cell →
      other = (producer, start+7) ∨ WriteBefore l X other (producer, start+7) ∨
        ReadBefore l X .ld read other := by
  intro other hOther
  by_cases hBlock : ∃ step : Fin 8, other = (producer, start+step.val)
  · obtain ⟨step, rfl⟩ := hBlock
    by_cases he : step = 7
    · subst step
      exact .inl rfl
    · have hlt : step.val < (7 : Fin 8).val := by
        have hBound := step.isLt
        have hn : step.val ≠ 7 := fun h => he (Fin.ext h)
        omega
      exact .inr (.inl (firstQkFragmentsBefore hg stage hIssues hlt))
  · exact .inr (hOutside other (scoreWriteCases hX hOther)
      (fun step he => hBlock ⟨step, he⟩))

/-- Each accumulating fragment reads its predecessor. Within one block the same-D pipeline
orders the earlier writes before that source and the subsequent writes after this read. -/
theorem firstQkAccumulatorSource (hX : Consistent l kernel Assumptions.all m X)
    {producer start use : Nat} (hg : producer < l.threads) (stage : Fin 2) (step : Fin 8)
    (hStep : step.val ≠ 0)
    (hIssues : ∀ k : Fin 8, X.get (producer, start+k.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) k use)) (cell : Cell)
    (hWrite : X.MmaCell (producer, start+(step.val-1)) cell)
    (hOutside : ∀ other, (X.MmaCell other cell ∨ StoreCell l X other cell) →
      (∀ k : Fin 8, other ≠ (producer, start+k.val)) →
      WriteBefore l X other (producer, start+(step.val-1)) ∨
        ReadBefore l X .acc (producer, start+step.val) other)
    (hLive : SourceLive l X (producer, start+(step.val-1)) (producer, start+step.val) cell) :
    ReadSource l X .acc (producer, start+(step.val-1)) (producer, start+step.val) cell := by
  let prev : Fin 8 := ⟨step.val-1, by have := step.isLt; omega⟩
  have hPrev : prev.val = step.val-1 := rfl
  have hlt : prev.val < step.val := by omega
  refine ⟨?_, .inl hWrite, firstQkFragmentsBefore hg stage hIssues hlt, ?_, hLive⟩
  · intro he
    have hn := congrArg Prod.snd he
    omega
  · intro other hOther
    by_cases hBlock : ∃ k : Fin 8, other = (producer, start+k.val)
    · obtain ⟨k, rfl⟩ := hBlock
      rcases lt_trichotomy k.val prev.val with hEarly | hSame | hLater
      · exact .inr (.inl (firstQkFragmentsBefore hg stage hIssues hEarly))
      · exact .inl (by rw [hSame, hPrev])
      · rcases Nat.eq_or_lt_of_le (show step.val ≤ k.val by omega) with hAt | hAfter
        · exact .inr (.inr (.inl (by rw [hAt])))
        · exact .inr (.inr (.inr (.inr (firstQkFragmentsPipe hg stage hIssues hAfter))))
    · exact .inr (hOutside other (scoreWriteCases hX hOther)
        (fun k hk => hBlock ⟨k, hk⟩))

end PTX.Kernels.TmlFa4Fwd.Softmax

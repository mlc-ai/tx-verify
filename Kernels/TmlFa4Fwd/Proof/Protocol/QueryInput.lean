-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.InputCredits
public import Kernels.TmlFa4Fwd.Proof.MmaOperandOrder
public import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
import Lemmas.Async.AsyncMBarrier
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryInputOrder
public import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory
import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner
import Lemmas.Protocol.PairTmaRing.Order
import Lemmas.Protocol.UnitGate
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy PTX.MBarrier
open Thread.Output (queryObject queryWaitMmaAfterInput)

noncomputable section

/-- A successful acquire of a query stage in the waiter's CTA. -/
def QueryAcquire (l : Launch) (X : Execution) (wait : EvId) (stage : Fin 2) : Prop :=
  ∃ e parity, X.get wait = some e ∧
    e.kind = .wait (queryObject l (wait.1 / l.block) stage) parity true true .cta

/-- The query acquire's actual record observed this completed phase. -/
def QueryAcquirePhase (l : Launch) (X : Execution) (wait : EvId)
    (stage : Fin 2) (phase : Nat) : Prop :=
  let log := X.objects (queryObject l (wait.1 / l.block) stage)
  ∃ j r, log[j]? = some r ∧ r.id = .thread wait ∧ observedAt log j = some phase

/-- The query box's actual completion was credited in this phase. -/
def QueryNotifyPhase (l : Launch) (X : Execution) (tensor : EvId)
    (stage : Fin 2) (phase : Nat) : Prop :=
  let log := X.objects (queryObject l (tensor.1 / l.block) stage)
  ∃ j r, log[j]? = some r ∧ r.id = .async tensor (.notify .load) ∧
    r.fault = none ∧ phaseAt log j = some phase

private theorem QueryAcquire.event {l : Launch} {X : Execution} {wait : EvId} {stage : Fin 2}
    (h : QueryAcquire l X wait stage) :
    ∃ site parity, X.get wait =
      some ⟨site, .wait (queryObject l (wait.1 / l.block) stage) parity true true .cta⟩ := by
  obtain ⟨⟨site, kind⟩, parity, he, hk⟩ := h
  change kind = _ at hk
  subst kind
  exact ⟨site, parity, he⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The successful acquire observes a clean, same-phase completion of one query subbox. -/
theorem QueryAcquire.observesTensor {tensor wait : EvId} {stage : Fin 2} {phase : Nat}
    (hCta : tensor.1 / l.block = wait.1 / l.block) (hWait : QueryAcquire l X wait stage)
    (hPhase : QueryAcquirePhase l X wait stage phase)
    (hNotify : QueryNotifyPhase l X tensor stage phase) :
    AsyncObserved X tensor (.notify .load) wait true .cta := by
  obtain ⟨site, parity, he⟩ := hWait.event
  obtain ⟨i, note, hi, hNote, hClean, hPhaseNote⟩ := hNotify
  obtain ⟨j, poll, hj, hPoll, hPhaseWait⟩ := hPhase
  let loc := queryObject l (wait.1 / l.block) stage
  change (X.objects (queryObject l (tensor.1 / l.block) stage))[i]? = some note at hi
  change phaseAt (X.objects (queryObject l (tensor.1 / l.block) stage)) i = some phase at hPhaseNote
  rw [hCta] at hi hPhaseNote
  have hm := List.mem_of_getElem? hi
  have ho := hX.tma.2.2.1 loc
  have hAction : ∃ n, note.action = .completeTx n := by
    have hSource := record_source hX.tma.2.2.1 hm
    cases hSource <;> first
      | exact ⟨_, ‹note.action = .completeTx _›⟩
      | grind
  obtain ⟨n, hComplete⟩ := hAction
  have hBytes := completedInputBytes hp hX hm hComplete
  have hObject := (ho.2.1 note hm).1
  rw [hNote, hComplete, hBytes] at hObject
  obtain ⟨j', poll', hj', hPoll', _, hPollClean, hSuccess⟩ := actualPollRecordClean hp hX he
  have heq : j' = j := ObjectInit.checked_record_index_eq ho.1 hj' hj (hPoll'.trans hPoll.symm)
  subst j'
  obtain rfl := Option.some.inj (hj'.symm.trans hj)
  have hNo := objects_noInval hX.tma.2.2.1 (fun e _ => noMbarInval hX (i := e)) loc
  have hOrder := MbarRing.Slot.updateBeforeWait_of_phase ho.1 hNo hi hClean hj hPollClean
    hSuccess hPhaseNote hPhaseWait
  rw [hNote, hPoll] at hOrder
  exact PairTmaRing.tensorObserved_of_notified hX hObject he hOrder

/-- The acquired Q byte precedes an actual operand A read issued later by the waiting lane. -/
theorem queryBeforeOperand {tensor wait mma : EvId} {stage : Fin 2}
    {phase address x y k d index : Nat} {s : TensorCopy.Spec} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} {loc : Loc} (hTensor : X.TensorIssue tensor address s)
    (hObject : s.mbar = queryObject l (wait.1 / l.block) stage)
    (hWait : QueryAcquire l X wait stage) (hPhase : QueryAcquirePhase l X wait stage phase)
    (hNotify : QueryNotifyPhase l X tensor stage phase) (hEarlier : TraceBefore X wait mma)
    (hWrite : TensorCopy.writeLoc s x y k = some loc) (hMma : X.MmaIssue mma d op accum mask)
    (hRead : op.byteLoc .a index = some loc) :
    modelCausality l X loc (.async tensor (.write (.load x y k)))
      (.async mma (.mmaRead false index)) := by
  have hCta : tensor.1 / l.block = wait.1 / l.block :=
    ((actualMbarOperand hp hX (Execution.UsesMbar.of_tensor hTensor)).1).symm.trans
      (congrArg Loc.cta hObject)
  have hObs := hWait.observesTensor hp hX hCta hPhase hNotify
  obtain ⟨_, hT⟩ := hTensor
  obtain ⟨_, _, hW⟩ := hWait.event
  obtain ⟨_, hM⟩ := hMma
  have ht := Step.CtaBar.thread_lt_of_get hX hT
  have hw := Step.CtaBar.thread_lt_of_get hX hW
  have hm := Step.CtaBar.thread_lt_of_get hX hM
  have hSame : SameCta l tensor.1 wait.1 := ⟨ht, hw, hCta⟩
  have hSameMma : SameCta l tensor.1 mma.1 :=
    ⟨ht, hm, hEarlier.1 ▸ hCta⟩
  have hScope := MbarRing.Unit.Gate.scopesMeet hSame .cluster .cta
  have hDone : AsyncFinished l X tensor (.write (.load x y k)) wait := by
    exact .inr ⟨.cta, by simpa only [AsyncObserved, Notifies, Part.target] using hObs, hScope⟩
  have hOrder : baseCausality l X wait mma :=
    .single (.inl (po_of_not_access hEarlier.1 hEarlier.2.1 hEarlier.2.2 (by rw [hM]; rfl)))
  exact Mma.tensorBeforeOperand hSameMma ⟨_, hT⟩ hWrite ⟨_, hM⟩ hRead hDone hOrder

/-- A QK operand A byte has its mathematical Q value after the matching stage acquire,
provided the other writes to that location are ordered outside this producer-consumer pair. -/
theorem qkQueryOperandSource (hFrame : OutputFootprint p X) {tensor wait mma : EvId} (block : Fin 4)
    (step : Fin 8) {use absoluteRow head d phase : Nat} (hh : head < p.heads) {accum : Bool}
    {mask : List Nat} {row k byte : Nat} (hr : row < 128) (hk : k < 16) (hb : byte < 2)
    (hWait : QueryAcquire l X wait (Mma.qkStage block))
    (hPhase : QueryAcquirePhase l X wait (Mma.qkStage block) phase)
    (hNotify : QueryNotifyPhase l X tensor (Mma.qkStage block) phase)
    (hEarlier : TraceBefore X wait mma)
    (hMma : X.MmaIssue mma d (Mma.qkOperands l mma.1 block step use) accum mask) :
    let barrier := queryObject l (wait.1 / l.block) (Mma.qkStage block)
    let base := Mma.qStart l (Mma.qkStage block) + 16384 * Mma.qkPlane step
    let spec := qInputSpec p (64 * Mma.qkPlane step) absoluteRow head
      ⟨.shared, mma.1 / l.block, base⟩ barrier false
    let slot := Mma.qkQSlot p step hr hk hb
    let loc := spec.sharedLoc slot
    let w := Ref.async tensor (.write (.load slot.1.val row byte))
    let r := Ref.async mma (.mmaRead false (Mma.qkByteIndex row k byte))
    X.TensorIssue tensor p.qMapAddress spec →
    (∀ other access bytes, X.MemWrites other access bytes → access.Covers loc →
      other = w ∨ modelCausality l X loc other w ∨ modelCausality l X loc r other) →
    Mma.OperandByteSource l X mma false (Mma.qkByteIndex row k byte) loc
      ((Value.float .bf16 (if absoluteRow + row < p.totalQ then
        p.q (absoluteRow + row) head (64 * Mma.qkPlane step + Mma.qkPlaneColumn step k)
        else 0)).byteAt byte) := by
  dsimp only
  intro hTensor hOther
  let barrier := queryObject l (wait.1 / l.block) (Mma.qkStage block)
  let base := Mma.qStart l (Mma.qkStage block) + 16384 * Mma.qkPlane step
  let spec := qInputSpec p (64 * Mma.qkPlane step) absoluteRow head
    ⟨.shared, mma.1 / l.block, base⟩ barrier false
  let slot := Mma.qkQSlot p step hr hk hb
  have ht : X.TensorIssue tensor p.qMapAddress spec := hTensor
  have hCta : tensor.1 / l.block = wait.1 / l.block :=
    ((actualMbarOperand hp hX (Execution.UsesMbar.of_tensor ht)).1).symm
  have hObs := hWait.observesTensor hp hX hCta hPhase hNotify
  obtain ⟨o, _, ho, hActual, hDone, _⟩ := hObs.tensor
  have hs : o.spec = spec := by
    obtain ⟨_, hGet⟩ := hActual
    obtain ⟨_, hGet'⟩ := ht
    exact (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (hGet.symm.trans hGet')))).2
  have hRead := Mma.qkQInputSlot hp mma.1 block step use absoluteRow head barrier false hr hk hb
  have hWrite : TensorCopy.writeLoc spec slot.1.val row byte = some (spec.sharedLoc slot) := by
    have hSlot : TensorTransfer.slotAt spec.descriptor slot.1.val row byte = some slot :=
      TensorCopy.slotAt_self slot
    exact congrArg (Option.map spec.sharedLoc) hSlot
  have hOrder := queryBeforeOperand hp hX ht rfl hWait hPhase hNotify hEarlier hWrite hMma hRead
  exact Mma.qkQueryByteSource hp hX hFrame mma.1 block step absoluteRow head hh barrier false
    hr hk hb ho hDone hs hOrder hOther

end
end PTX.Kernels.TmlFa4Fwd.Protocol

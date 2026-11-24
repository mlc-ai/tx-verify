-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReuseOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyReleaseOrder
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyValues
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyStaging
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyPublicationGroup
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyOrdinal
import Lemmas.Async.AsyncChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy PTX.MBarrier
open Thread.Mma.Observation (emptyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A successful parity-zero empty wait must have observed a released generation. -/
theorem observedPhaseOfZeroEmptyAcquire {wait : EvId} {slot : Fin 3}
    (hWait : Thread.Loader.EmptyAcquire l X wait slot 0) :
    ∃ (position phase : Nat) (poll : Record Ref),
      (X.objects (emptyObject l wait.1 slot))[position]? = some poll ∧
      poll.id = .thread wait ∧ poll.reply.waited = some true ∧
      observedAt (X.objects (emptyObject l wait.1 slot)) position = some phase := by
  obtain ⟨position, poll, hAt, hId, hAction, _, hSuccess⟩ := hWait.record hp hX
  obtain ⟨state, parity, _, hParity, hOpposite, hCompleted⟩ :=
    (X.objects_checked hX (emptyObject l wait.1 slot)).okPoll hAt hSuccess
  rw [hAction] at hParity
  obtain rfl := (Action.pollParity.inj hParity).1.symm
  have hPositive : 0 < state.phase := by omega
  refine ⟨position, state.phase - 1, poll, hAt, hId, hSuccess, ?_⟩
  change ((X.objects (emptyObject l wait.1 slot))[position]?.bind (·.reply.completed)) = _
  change (X.objects (emptyObject l wait.1 slot))[position]? = some poll at hAt
  rw [hAt, Option.bind_some, hCompleted, ite_eq_left hPositive]

/-- A selected vector from the actual publication observed by an operand's ready
acquire writes the byte before that operand is read. -/
theorem LoaderReady.Completed.publishedCacheCopyBeforeOperand {wait mma issue : EvId} {slot : Fin 3}
    {phase d index j : Nat} {loc : Loc} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    {s : Spec} (h : LoaderReady.Completed l X wait slot phase)
    (hPub : X.AsyncArrive issue (Thread.Loader.readyObject l wait.1 slot) true)
    (hRank : LoaderReady.generation l X issue slot = phase)
    (group : Thread.Loader.PublishedCopyGroup l X issue) (hMember : (j, s) ∈ group.copies)
    (hCover : s.dst.Covers loc) (hMma : X.MmaIssue mma d op accum mask)
    (hAfter : TraceBefore X wait mma) (hLoc : op.byteLoc .b index = some loc) :
    (∃ bytes, X.MemWrites (.async (issue.1, j) (.write .copy)) s.dst bytes) ∧
      modelCausality l X loc (.async (issue.1, j) (.write .copy))
        (.async mma (.mmaRead true index)) := by
  obtain ⟨lane, hLane⟩ := Thread.Loader.publicationProducer hp hX hPub
  obtain ⟨actual, actualGroup, hActualLane, hActual, hPhase, hCopies⟩ :=
    h.actualCopyGroupBeforeOperand hp hX (isB := true) (index := index) lane hMma hAfter hLoc
  have hSame := Thread.Loader.publicationUniqueAtSlot hp hX hPub hActual
    (hLane.trans hActualLane.symm) (hRank.trans hPhase.symm)
  subst actual
  obtain ⟨pair, upper, hDest⟩ := group.destination hp hX hPub hMember
  obtain ⟨j', t, hMember', hDst⟩ := actualGroup.coverage hp hX hActual pair upper
  dsimp only at hDest hDst
  rw [group.slotFor hp hX hPub, ← actualGroup.slotFor hp hX hActual, ← hDst] at hDest
  have hCover' := hDest ▸ hCover
  obtain ⟨_, hIdx⟩ := LoaderReady.coveringCopyUniqueInGeneration hp hX group actualGroup
    hPub hActual rfl hMember hMember' hCover hCover'
  subst j'
  have hSpec : s = t := by
    obtain ⟨_, hCopy⟩ := ((group.member j s).mp hMember).2.2
    obtain ⟨_, hCopy'⟩ := ((actualGroup.member j t).mp hMember').2.2
    exact Kind.copy.inj (congrArg Event.kind (Option.some.inj (hCopy.symm.trans hCopy')))
  exact hSpec.symm ▸ hCopies j t hMember' hCover'

end PTX.Kernels.TmlFa4Fwd.Protocol

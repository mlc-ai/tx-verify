-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CacheCopyOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOutputReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.TensorInputReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCacheOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyStaging
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialValueStaging

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy

/-- A ready acquire for one cache slot generation and the consuming fragment
before the output commit. This predicate records observations of the same byte. -/
def CacheUseBeforeCommit (l : Launch) (X : Execution) (commit : EvId) (slot : Fin 3)
    (phase : Nat) (loc : Loc) : Prop :=
  ∃ (ready mma : EvId) (d : Nat) (operands : TcMma.OperandSpec)
      (accum : Bool) (mask : List Nat) (index : Nat),
    Nonempty (LoaderReady.Completed l X ready slot phase) ∧
    TraceBefore X ready mma ∧ TraceBefore X mma commit ∧
    X.MmaIssue mma d operands accum mask ∧ operands.byteLoc .b index = some loc

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem copyByteAboveFirstStaging {copy : EvId} {s : Spec} {loc : Loc}
    (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc) :
    l.sharedBase + 68608 ≤ loc.addr := by
  obtain ⟨_, slot, pair, upper, hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  have hCovers := hCover
  rw [hDst] at hCovers
  let addr := kvCopyAddress l.sharedBase slot (copy.1 % l.block) pair upper
  have hLo : addr ≤ loc.addr := hCovers.2.2.1
  have hHi : loc.addr < addr + 16 := hCovers.2.2.2
  have hByte : loc.addr - addr < 16 := by omega
  have hRange := kvCopyAddress_range (lane := copy.1 % l.block) (upper := upper)
    hp.shared.1 slot.isLt pair.isLt hByte
  exact (Nat.add_sub_of_le hLo) ▸ hRange.1

/-- An ordinary cache vector can overlap only the second stage's staging writer,
and the destination identifies its CTA. -/
theorem cacheOverlapStaging {copy writer : EvId} {s : Spec} {a : Acc} {data : List Byte} {loc : Loc}
    (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc)
    (hWrite : Thread.Correction.StagingWrite X (.thread writer) a data) (hOther : a.Covers loc) :
    Thread.StageStagingWrite X writer 1 a data ∧ copy.1 / l.block = writer.1 / l.block := by
  obtain ⟨stage, box, col, row, hCol, hRow, hAccess, hStage⟩ := hWrite.stageElement hp hX
  have hStagingCover := hAccess ▸ hOther
  have hLimit := Thread.Output.elementStageRange hCol hRow hStagingCover
  have hBase := copyByteAboveFirstStaging hp hX hCopy hCover
  have hStageOne : stage = 1 := by
    fin_cases stage
    · have hUpper := hLimit.2
      change loc.addr < l.sharedBase + 3072 + 65536 * (0 + 1) at hUpper
      omega
    · rfl
  subst stage
  obtain ⟨_, _, _, _, hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  rw [hDst] at hCover
  exact ⟨hStage, hCover.2.1.symm.trans hStagingCover.2.1⟩

/-- An ordinary copy's order to the actual correction staging store extends to the
pending O read. The same-stage premise applies to any publication generation. -/
theorem cacheBeforePendingOutputAfterStaging {copy issue : EvId} {address x y byte : Nat}
    {loc : Loc} {s : Spec} {spec : TensorStore.Spec} (hCopy : X.Copy copy s)
    (hCover : s.dst.Covers loc) (hStore : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y byte = some loc)
    (hBefore : ∀ writer access data, Thread.StageStagingWrite X writer 1 access data →
      access.Covers loc → copy.1 / l.block = writer.1 / l.block →
      ByteCausality l X loc (.async copy (.write .copy)) (.thread writer)) :
    ByteCausality l X loc (.async copy (.write .copy))
      (.async issue (.read (.store x y byte))) := by
  obtain ⟨_, hSame, _, _, _, _⟩ := cacheOverlap hp hX hStore hRead hCopy hCover
  obtain ⟨stage, writer, access, data, hStage, hOther, hWriter, hRangeStage, _, _, hOrder⟩ :=
    Thread.Output.actualPublishedStagingSource hp hX hStore hRead
  have hStageOne := hRangeStage.resolve_left
    (Nat.not_lt_of_ge (copyByteAboveFirstStaging hp hX hCopy hCover))
  subst stage
  have hStaging := hBefore writer access data hStage hOther (hSame.trans hWriter.symm)
  obtain ⟨_, hCopyEvent⟩ := hCopy
  obtain ⟨_, hStoreEvent⟩ := hStore
  have hCta : SameCta l copy.1 issue.1 :=
    ⟨PTX.Proof.event_thread_lt hX hCopyEvent, PTX.Proof.event_thread_lt hX hStoreEvent, hSame⟩
  exact .direct (asyncSourceBeforePublishedRead hX hCta hStaging hOrder)

end PTX.Kernels.TmlFa4Fwd.Protocol.Output

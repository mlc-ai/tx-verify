-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStats
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.AsyncCopy Correction PTX.Kernels.TmlFa4Fwd.Loader Prologue

noncomputable section

private theorem statsByteBeforeData (l : Launch) (g : Nat) (stage : Fin 2)
    (kind : StatsKind) {k : Nat} (hk : k < 4) :
    ((statsLoc l g stage kind).at k).addr < l.sharedBase + 3072 := by
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  cases kind <;> simp only [statsLoc, Loc.at, statsOff] <;> omega

private theorem tensorInputWriteAddress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i addr s)
    {x y k : Nat} {dest : Loc} (hw : TensorCopy.writeLoc s x y k = some dest) :
    l.sharedBase + 3072 ≤ dest.addr := by
  obtain ⟨site, _, _, _, hBase, _, _⟩ := actualInputBox hp hX hi
  have hOffset : 3072 ≤ (inputSite site).sharedOffset := by fin_cases site <;> decide
  unfold TensorCopy.writeLoc at hw
  obtain ⟨slot, _, rfl⟩ := Option.map_eq_some_iff.mp hw
  change l.sharedBase + 3072 ≤ s.sharedBase.addr + _
  rw [hBase]
  change l.sharedBase + 3072 ≤ l.sharedBase + (inputSite site).sharedOffset + _
  omega

theorem cacheCopyWriteLower {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {s : AsyncCopy.Spec} (hCopy : X.Copy i s) :
    l.sharedBase + 68608 ≤ s.dst.loc.addr := by
  obtain ⟨pc, he⟩ := hCopy
  obtain ⟨hLo, hHi, hAt⟩ := actualCopyAtInLoader hX he
  obtain ⟨site, hlo, hhi⟩ := loaderCopyPcInPacket hLo hHi hAt
  obtain ⟨pair, upper, rfl⟩ := actualPacketCopyCoordinates hX site hlo hhi he
  rcases i with ⟨g, j⟩
  obtain ⟨slot, hDst⟩ := actualCopyPrefixDestination hp hX site pair upper he
  rw [hDst]
  simpa only [Nat.add_zero] using
    (kvCopyAddress_range (lane := g % l.block) (upper := upper) (byte := 0)
      hp.shared.1 slot.isLt pair.isLt (by decide)).1

/-- A performed shared write is an ordinary access, a tensor input or a whole cache copy. -/
theorem sharedWriteSource {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {w : Ref} {a : Acc} {bytes : List Byte} {loc : Loc} (hw : X.MemWrites w a bytes)
    (hCover : a.Covers loc) (hLocal : loc.space = .shared) :
    (∃ i, w = .thread i ∧ X.Writes i a bytes) ∨
      (∃ i x y k, w = .async i (.write (.load x y k))) ∨
      ∃ i s, w = .async i (.write .copy) ∧ X.Copy i s ∧ a = s.dst := by
  have hShared : a.loc.space = .shared := hCover.1.symm.trans hLocal
  cases w with
  | thread i =>
    rcases hw with he | ⟨old, he⟩
    · exact .inl ⟨i, rfl, he⟩
    · exact (noActualRmw hX he).elim
  | async i part =>
    cases part <;> try exact False.elim hw
    case writeStore x y idx =>
      obtain ⟨_, _, _, _, _, hLoc, _⟩ := hw
      rw [Execution.store_writeLoc_global hLoc] at hShared
      cases hShared
    case writeLoad x y idx =>
      exact .inr (.inl ⟨i, x, y, idx, rfl⟩)
    case writeCta c =>
      obtain ⟨_, _, hIssue, _⟩ := hw
      exact (noClcIssue hX hIssue).elim
    case writeCopy =>
      obtain ⟨s, hCopy, _, rfl, _⟩ := hw
      exact .inr (.inr ⟨i, s, rfl, hCopy, rfl⟩)
    case writeElem j =>
      obtain ⟨s, hCopy, he, _⟩ := hw
      simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (actualCopyShape hX hCopy).whole]
        at he

/-- Below the cache buffers, a performed shared write is an ordinary access or a tensor input. -/
theorem sharedWriteBeforeCache {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {w : Ref} {a : Acc} {bytes : List Byte} {loc : Loc} (hw : X.MemWrites w a bytes)
    (hCover : a.Covers loc) (hLocal : loc.space = .shared)
    (hBefore : loc.addr < l.sharedBase + 68608) :
    (∃ i, w = .thread i ∧ X.Writes i a bytes) ∨
      ∃ i x y k, w = .async i (.write (.load x y k)) := by
  rcases sharedWriteSource hX hw hCover hLocal with hThread | hInput | ⟨i, s, _, hCopy, rfl⟩
  · exact .inl hThread
  · exact .inr hInput
  · have hLower := (cacheCopyWriteLower hp hX hCopy).trans hCover.2.2.1
    omega

/-- All performed writes covering one terminal statistics byte are ordinary thread writes.
Tensor input and KV copy destinations lie above the statistics region. -/
theorem terminalStatisticsWriterOrdinary {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {stage : Fin 2} {kind : StatsKind} {k : Nat} (hk : k < 4)
    {w : Ref} {a : Acc} {bytes : List Byte} (hw : X.MemWrites w a bytes)
    (hCover : a.Covers ((statsLoc l g stage kind).at k)) :
    ∃ i, w = .thread i ∧ X.Writes i a bytes := by
  have hStats := statsByteBeforeData l g stage kind hk
  obtain hOrdinary | ⟨i, x, y, byte, rfl⟩ := sharedWriteBeforeCache hp hX hw hCover rfl (by omega)
  · exact hOrdinary
  · obtain ⟨_, _, _, _, he, hLoc, _⟩ := hw
    have hLower := tensorInputWriteAddress hp hX he hLoc
    have hVal := hCover.2.2.1
    omega

end
end PTX.Kernels.TmlFa4Fwd.Thread

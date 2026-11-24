-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.OrdinarySharedConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsKinds
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsOutput
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsOperands
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.GlobalConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
public import Lemmas.Order.Order

public section

/-! # Byte causality for every conflicting pair -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow PTX.AsyncCopy AsyncSharedConflicts

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem thread_async {i j : EvId} {p : Part} {a b : Acc} {l : Loc}
    {we wf : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.Intent (.thread i) a we) (hf : X.Intent (.async j p) b wf)
    (hWrite : we = true ∨ wf = true) (ha : a.Covers l) (hb : b.Covers l)
    (hShared : l.space = .shared) :
    ByteCausality L X l (.thread i) (.async j p) ∨
      ByteCausality L X l (.async j p) (.thread i) := by
  cases shared_async_kind hX hf hb hShared
  case load =>
    exact (load_write_thread_ordered hpre hX hs ht hf hb he ha).symm
  case output =>
    have hWrite : we = true := by simpa using hWrite
    cases hWrite
    exact .inl (output_read_after_thread_write hpre hX hs ht hf hb he ha)
  case operand =>
    have hWrite : we = true := by simpa using hWrite
    cases hWrite
    exact operand_thread_write_ordered hpre hX hs ht hf hb he ha

private theorem async_async {i j : EvId} {p q : Part} {a b : Acc} {l : Loc}
    {we wf : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hne : Ref.async i p ≠ .async j q)
    (he : X.Intent (.async i p) a we) (hf : X.Intent (.async j q) b wf)
    (hWrite : we = true ∨ wf = true) (ha : a.Covers l) (hb : b.Covers l)
    (hShared : l.space = .shared) :
    ByteCausality L X l (.async i p) (.async j q) ∨
      ByteCausality L X l (.async j q) (.async i p) := by
  have hKindE := shared_async_kind hX he ha hShared
  have hKindF := shared_async_kind hX hf hb hShared
  cases hKindE <;> cases hKindF
  all_goals
    first
    | exact load_writes_ordered hpre hX hs ht he ha hf hb hne
    | exact .inl (load_write_operand_ordered hpre hX hs ht he ha hf hb)
    | exact .inr (load_write_operand_ordered hpre hX hs ht hf hb he ha)
    | exact (load_write_output_read_disjoint hpre hX hs ht he ha hf hb).elim
    | exact (load_write_output_read_disjoint hpre hX hs ht hf hb he ha).elim
    | simp at hWrite

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- Every conflicting pair in shared memory is ordered at the covered byte, including
asynchronous stages that have only been issued. -/
theorem shared_conflict_ordered (hResource : ¬ Tmem.Pair.ResourceUnsafe L X) {e f : Ref} {a b : Acc}
    {l : Loc} (hConflict : Conflict X e f a b) (ha : a.Covers l) (hb : b.Covers l)
    (hShared : l.space = .shared) :
    ByteCausality L X l e f ∨ ByteCausality L X l f e := by
  have ⟨hne, we, wf, he, hf, hWrite, _⟩ := hConflict
  cases e with
  | thread i =>
    cases f with
    | thread j =>
      exact OrdinarySharedConflicts.ordinary_conflict_ordered hpre hX hs ht
        hResource hConflict ha hb hShared
    | async j q => exact thread_async hpre hX hs ht he hf hWrite ha hb hShared
  | async i p =>
    cases f with
    | thread j => exact (thread_async hpre hX hs ht hf he hWrite.symm hb ha hShared).symm
    | async j q => exact async_async hpre hX hs ht hne he hf hWrite ha hb hShared

private theorem writer_space {ref : Ref} {a : Acc} {l : Loc} (hw : X.Intent ref a true)
    (ha : a.Covers l) :
    l.space = .global ∨ l.space = .shared := by
  cases ref with
  | thread i =>
    have hNoRmw : ∀ tag access old bytes, X.get i ≠ some ⟨tag, .rmw access old bytes⟩ :=
      fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩
    rcases (Execution.access_iff_of_not_rmw hNoRmw).mp hw with ⟨_, _, hFalse⟩ | ⟨_, he, _⟩
    · cases hFalse
    · exact (RawSharedWrites.ordinary_window hpre hX hs ht he ha).imp id And.left
  | async i p =>
    have ⟨hp, hf⟩ := hw
    cases p <;> try contradiction
    case writeCopy =>
      obtain ⟨_, hCopy, _⟩ := hf
      exact (GlobalWrites.no_copy hX hCopy).elim
    case writeElem =>
      obtain ⟨_, hCopy, _⟩ := hf
      exact (GlobalWrites.no_copy hX hCopy).elim
    case writeCta =>
      obtain ⟨_, _, hClc, _, _⟩ := hf
      exact (GlobalWrites.no_clc hX hClc).elim
    case writeLoad =>
      exact .inr (load_write_window hpre hX hs ht hw ha).1
    case writeStore =>
      obtain ⟨_, _, _, hLoc, _⟩ := hf
      unfold TensorStore.writeLoc at hLoc
      obtain ⟨_, _, hDest⟩ := Option.bind_eq_some_iff.mp hLoc
      obtain ⟨_, _, hAddr⟩ := Option.map_eq_some_iff.mp hDest
      exact .inl (ha.1.trans (congrArg Loc.space hAddr).symm)

/-- Every potential memory conflict is ordered on each overlapping byte. -/
theorem memory_conflict_ordered {e f : Ref} {a b : Acc} {l : Loc} (hConflict : Conflict X e f a b)
    (ha : a.Covers l) (hb : b.Covers l) :
    ByteCausality L X l e f ∨ ByteCausality L X l f e := by
  have ⟨_, we, wf, he, hf, hW, _⟩ := hConflict
  have hSpace : l.space = .global ∨ l.space = .shared := by
    rcases hW with rfl | rfl
    · exact writer_space hpre hX hs ht he ha
    · exact writer_space hpre hX hs ht hf hb
  rcases hSpace with hGlobal | hShared
  · exact (no_global_conflict hpre hX hs ht hGlobal hConflict ha hb).elim
  · exact shared_conflict_ordered hpre hX hs ht (no_resourceUnsafe hpre hX hs ht)
      hConflict ha hb hShared

/-- Conflicts at every byte touched by a read are ordered in the tracked kernel. -/
theorem reads_ordered :
    ReadsOrdered L X :=
  fun _ _ _ _ _ _ _ _ _ _ hConflict _ ha hb =>
    memory_conflict_ordered hpre hX hs ht hConflict ha hb

/-- Neither a same-footprint race nor an unordered mixed-size overlap is possible. -/
theorem no_memory_conflicts :
    ¬ Race L X ∧ ¬ Mixed L X := by
  constructor
  · rintro ⟨e, f, a, b, l, hc, hSame, ha, _, hef, hfe, _⟩
    exact (memory_conflict_ordered hpre hX hs ht hc ha ((hSame.covers l).mp ha)).elim hef hfe
  · rintro ⟨e, f, a, b, l, hc, _, ha, hb, hef, hfe⟩
    exact (memory_conflict_ordered hpre hX hs ht hc ha hb).elim hef hfe

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

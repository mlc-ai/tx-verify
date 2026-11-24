-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Output
public import Kernels.InklingRelDecode.Proof.Launch
public import Kernels.InklingRelDecode.Proof2.Lib.EpiMeans
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotClc

@[expose] public section

/-!
# The frame of `Post`: every global write is inside an output array

The kernel has no atomic read-modify-write, no bulk copy, no tensor store and no cancellation
request (`decide` over the decoded program), and a tensor load writes shared memory (the memory
model's `TensorOk`). So a write of an execution to global memory is a thread's generic store
(`global_write_thread`), and by `global_wr_state` an epilogue store, which lies in `OPart` or
`LsePart` (`global_write_in_arrays`). Every global byte outside the two arrays keeps its launch
content (`post_frame`, the last conjunct of `Post`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem kernel_noAtomic : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

theorem kernel_noBulk : kernel.code.all (fun ins => !bulkOp ins.op) = true := by
  decide +kernel

theorem kernel_noClc : kernel.code.all (fun ins => !clcOp ins.op) = true := by
  decide +kernel

theorem kernel_noTensorStore : kernel.code.all (fun ins => !tensorStoreOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no atomic read-modify-write.** -/
theorem no_rmw (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {a : Acc} {old : List (Option Byte)} {new : Option (List Byte)},
      X.get i ≠ some ⟨pc, .rmw a old new⟩ :=
  fun he => no_kind_of_code hX atomicOp (fun k => ∃ a o n, k = .rmw a o n)
    (fun _ ⟨_, _, _, h⟩ => by cases h) (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk)
    kernel_noAtomic he ⟨_, _, _, rfl⟩

/-- **The kernel has no asynchronous copy.** -/
theorem no_copy (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩ :=
  fun he => no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk)
    kernel_noBulk he ⟨_, rfl⟩

/-- **The kernel has no cancellation request.** -/
theorem no_clc (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {s : Clc.Spec} {t : List Nat},
      X.get i ≠ some ⟨pc, .clcIssue s t⟩ :=
  fun he => no_kind_of_code hX clcOp (fun k => ∃ s t, k = .clcIssue s t)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk)
    kernel_noClc he ⟨_, _, rfl⟩

/-- **The kernel has no tensor store.** -/
theorem no_tensorStore (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc a : Nat} {s : TensorStore.Spec},
      X.get i ≠ some ⟨pc, .tensorStore a s⟩ :=
  fun he => no_kind_of_code hX tensorStoreOp (fun k => ∃ a s, k = .tensorStore a s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_tensorStore_op hf hk)
    kernel_noTensorStore he ⟨_, _, rfl⟩

/-- **A global write is a thread's generic store**: no atomic, copy, tensor store or
cancellation response writes global memory, and a tensor load writes shared memory. -/
theorem global_write_thread (hX : Consistent L kernel asms mem0 X) {w : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} (hw : X.MemWrites w a bs) (hsp : a.loc.space = .global) :
    ∃ g n pc, w = .thread (g, n) ∧ X.get (g, n) = some ⟨pc, .wr a bs⟩ := by
  rcases w with e | ⟨i, part⟩
  · rcases hw with ⟨pc, h⟩ | ⟨old, pc, h⟩
    · exact ⟨e.1, e.2, pc, rfl, h⟩
    · exact absurd h (no_rmw hX)
  · exfalso
    cases part with
    | writeStore x y k =>
      obtain ⟨o, addr, b, -, ⟨pc, hi⟩, -⟩ := hw
      exact no_tensorStore hX hi
    | writeLoad x y z =>
      obtain ⟨o, addr, b, ho, -, hloc, -⟩ := hw
      have hs : o.spec.sharedBase.space = .shared := (hX.tensor i o ho).2.2.1.2.1
      simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hloc
      obtain ⟨slot, -, hl⟩ := hloc
      rw [← hl] at hsp
      simp only [TensorBox.sharedLoc] at hsp
      rw [hs] at hsp
      cases hsp
    | writeCta c =>
      obtain ⟨s, targets, ⟨pc, hi⟩, -⟩ := hw
      exact no_clc hX hi
    | writeCopy =>
      obtain ⟨s, ⟨pc, hb⟩, -⟩ := hw
      exact no_copy hX hb
    | writeElem j =>
      obtain ⟨s, ⟨pc, hb⟩, -⟩ := hw
      exact no_copy hX hb
    | _ => exact hw.elim

/-! ### The stores are inside the arrays -/

variable {g : Nat}

/-- **A global write is inside an output array**: it covers a byte of `OPart` or `LsePart`
only. -/
theorem global_write_in_arrays (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs)
    (hsp : a.loc.space = .global) {l : Loc} (hc : a.Covers l) :
    (Q.oBase ≤ l.addr ∧ l.addr < Q.oBase + oBytes Q) ∨
      (Q.lseBase ≤ l.addr ∧ l.addr < Q.lseBase + lseBytes Q) := by
  obtain ⟨g, n, pc, rfl, hget⟩ := global_write_thread hX hw hsp
  have hg := Frame.lt_of_get hX hget
  obtain ⟨d, -, -, hm, hrv, hcases⟩ := global_wr_state hpre hX hS ht hg hget hsp
  obtain ⟨hx, -, ht', hh⟩ := Epi.row_coords hpre hg hm hrv
  obtain ⟨-, -, h1, h2⟩ := hc
  rcases hcases with ⟨j, -, v, -, -, hacc⟩ | ⟨-, v, -, -, hacc⟩
  · subst hacc
    have hd : Epi.outCol0 L g + j.val < headDim := by
      have : Epi.halfM (g % L.block) ≤ 1 := by unfold Epi.halfM; omega
      have := j.isLt
      unfold Epi.outCol0 headDim
      omega
    have := oLoc_range (Q := Q) (Epi.outSplit L g) (Epi.outToken Q L g) (Epi.outHead L g) _ hx ht'
      hh hd
    left
    simp only [EvD.wordAcc] at h1 h2
    omega
  · subst hacc
    have := lseLoc_range (Q := Q) (Epi.outSplit L g) (Epi.outToken Q L g) (Epi.outHead L g) hx
      ht' hh
    right
    simp only [EvD.wordAcc] at h1 h2
    omega

/-- **The frame of `Post`'s last conjunct**: a global byte outside both output arrays keeps its
launch content. -/
theorem post_frame (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {m : FinalMem} (hfin : IsFinal L mem0 X m) :
    ∀ l, l.space = .global → ¬ (Q.oBase ≤ l.addr ∧ l.addr < Q.oBase + oBytes Q) →
      ¬ (Q.lseBase ≤ l.addr ∧ l.addr < Q.lseBase + lseBytes Q) → m l = mem0 l := by
  intro l hl ho hs
  apply hfin.unwritten
  intro w a bs hw hc
  have hsp : a.loc.space = .global := hc.1.symm.trans hl
  rcases global_write_in_arrays hpre hX hS ht hw hsp hc with h | h
  · exact ho h
  · exact hs h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
public import Lemmas.Flow.NotBulkPrefetch
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.NotTensorPrefetch
public import Lemmas.Protocol.Region

@[expose] public section

/-! # The asynchronous accessors of shared memory, from the code

Static scans of the decoded program, each evaluated once (`decide +kernel`): no bulk prefetch is
issued (`noBulkPrefetch`); every tensor store is at a pc of warpgroup 0's code, `[103, 1842)`
(`store_pc`), and every tensor load at a pc of the MMA or TMA warp's code, `[1850, 2332)`
(`load_pc`). With no linear copy (`noCopy`) and no cancellation request (`noClcIssue`), an
asynchronous access of a shared byte is an MMA operand read, a tensor store's source read or a
tensor load's destination write, each of one byte (`async_shared_ref`, from `shared_intent`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

private theorem noPrefetchCode : kernel.code.all (fun ins => !bulkPrefetchOp ins.op) = true := by
  decide +kernel

/-- No bulk prefetch is issued. -/
theorem noBulkPrefetch (hX : Consistent l kernel A m X) {i : EvId} {a : Acc}
    (h : X.BulkPrefetch i a) : False := by
  obtain ⟨_, he⟩ := h
  exact no_kind_of_code hX bulkPrefetchOp (fun k => ∃ a, k = .bulkPrefetch a)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulkPrefetch_op hf hk) noPrefetchCode he
    ⟨_, rfl⟩

private theorem noTensorPrefetchCode :
    kernel.code.all (fun ins => !tensorPrefetchOp ins.op) = true := by
  decide +kernel

/-- No tensor prefetch is issued. -/
theorem noTensorPrefetch (hX : Consistent l kernel A m X) {i : EvId} {a : Nat}
    {s : TensorPrefetch.Spec} (h : X.TensorPrefetchIssue i a s) : False := by
  obtain ⟨_, he⟩ := h
  exact no_kind_of_code hX tensorPrefetchOp (fun k => ∃ a s, k = .tensorPrefetch a s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_tensorPrefetch_op hf hk)
    noTensorPrefetchCode he ⟨_, _, rfl⟩

/-- Every instruction `p` selects is at a position in `[lo, hi)`. -/
private def InRange (p : Op → Bool) (lo hi : Nat) : Bool :=
  kernel.code.zipIdx.all fun x => !p x.1.op || (decide (lo ≤ x.2) && decide (x.2 < hi))

private theorem inRange_mem {p : Op → Bool} {lo hi : Nat} (h : InRange p lo hi = true) {pc : Nat}
    {ins : Instr} (hc : kernel.code[pc]? = some ins) (hp : p ins.op = true) :
    lo ≤ pc ∧ pc < hi := by
  have hmem : (ins, pc) ∈ kernel.code.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using hc
  have h' := List.all_eq_true.mp h (ins, pc) hmem
  simpa only [hp, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] using h'

private theorem storeRange : InRange tensorStoreOp 103 1842 = true := by decide +kernel
private theorem loadRange : InRange tensorOp 1850 2332 = true := by decide +kernel

/-- **A tensor store is warpgroup 0's**: its pc is in `[103, 1842)`. -/
theorem store_pc (hX : Consistent l kernel A m X) {i : EvId} {e : Event} (he : X.get i = some e)
    {a : Nat} {s : TensorStore.Spec} (hk : e.kind = .tensorStore a s) :
    103 ≤ e.pc ∧ e.pc < 1842 := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · rw [hk] at hf; cases hf
  · exact inRange_mem storeRange hc (fires_tensorStore_op hf hk)

/-- **A tensor load is the MMA or TMA warp's**: its pc is in `[1850, 2332)`. -/
theorem load_pc (hX : Consistent l kernel A m X) {i : EvId} {e : Event} (he : X.get i = some e)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    1850 ≤ e.pc ∧ e.pc < 2332 := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · rw [hk] at hf; cases hf
  · refine inRange_mem loadRange hc ?_
    cases hq : tensorOp ins.op
    · exact absurd hk (fires_notTensor (eventTmpl_notTensor hq) hf a s)
    · rfl

/-- The accessors an asynchronous stage may have at a shared byte: an MMA operand read, a tensor
store's source read or a tensor load's destination write, each of one byte. -/
abbrev AsyncShRef (X : Execution) (i : EvId) (p : AsyncCopy.Part) (a : Acc) : Prop :=
  (∃ isB idx, p = .mmaRead isB idx ∧ a.size = 1 ∧ X.MmaFootprint i isB idx a.loc) ∨
    (∃ x y k s addr, p = .read (.store x y k) ∧ X.TensorStoreIssue i addr s ∧
      TensorStore.readLoc s x y k = some a.loc ∧ a.size = 1) ∨
    (∃ x y k s addr, p = .write (.load x y k) ∧ X.TensorIssue i addr s ∧
      TensorCopy.writeLoc s x y k = some a.loc ∧ a.size = 1)

/-- **The asynchronous accessors of a shared byte**, each a one-byte footprint. -/
theorem async_shared_ref (hX : Consistent l kernel A m X) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {w : Bool} (h : X.Intent (.async i p) a w) {b : Loc} (hc : a.Covers b)
    (hs : b.space = .shared) : AsyncShRef X i p a := by
  rcases Execution.shared_intent h hc hs with ⟨e, he, -⟩ | ⟨i', isB, idx, he⟩ |
    ⟨i', x, y, k, he⟩ | ⟨i', x, y, k, he⟩ | ⟨i', c, s, tg, -, hi, -⟩ | ⟨i', q, s, -, hi⟩ |
    ⟨i', -, hi⟩
  · cases he
  · cases he
    obtain ⟨-, hsz, hf⟩ := h
    exact .inl ⟨isB, idx, rfl, hsz, hf⟩
  · cases he
    obtain ⟨-, s, addr, hi, hl, hsz⟩ := h
    exact .inr (.inl ⟨x, y, k, s, addr, rfl, hi, hl, hsz⟩)
  · cases he
    obtain ⟨-, s, addr, hi, hl, hsz⟩ := h
    exact .inr (.inr ⟨x, y, k, s, addr, rfl, hi, hl, hsz⟩)
  · exact (noClcIssue hX hi).elim
  · exact (noCopy hX hi).elim
  · exact (noBulkPrefetch hX hi).elim

/-- **The accessors of an asynchronous byte**, wherever it is: an MMA operand read, a tensor
store's source read, write or old-value read, or a tensor load's source read or destination
write, each of one byte. -/
theorem async_ref (hX : Consistent l kernel A m X) {i : EvId} {p : AsyncCopy.Part} {a : Acc}
    {w : Bool} (h : X.Intent (.async i p) a w) :
    AsyncShRef X i p a ∨
      (∃ x y k s addr, (p = .write (.store x y k) ∨ p = .old (.store x y k)) ∧
        X.TensorStoreIssue i addr s ∧ TensorStore.writeLoc s x y k = some a.loc ∧ a.size = 1) ∨
      (∃ x y k s addr, p = .read (.load x y k) ∧ X.TensorIssue i addr s ∧
        TensorCopy.readLoc s x y k = some a.loc ∧ a.size = 1) := by
  obtain ⟨-, hF⟩ := h
  rcases p with s | s | s | t | _ | _ | _ | _ | ⟨isB, idx⟩ | _ | _
  · rcases s with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j <;>
      simp only [Execution.AsyncFootprint] at hF
    · rcases hF with ⟨s, hc, -⟩ | hb
      · exact (noCopy hX hc).elim
      · exact (noBulkPrefetch hX hb).elim
    · obtain ⟨s, addr, hi, hl, hz⟩ := hF
      exact .inr (.inr ⟨x, y, k, s, addr, rfl, hi, hl, hz⟩)
    · obtain ⟨s, addr, hi, hl, hz⟩ := hF
      exact .inl (.inr (.inl ⟨x, y, k, s, addr, rfl, hi, hl, hz⟩))
    · obtain ⟨s, addr, hi, -⟩ := hF
      exact (noTensorPrefetch hX hi).elim
  · rcases s with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j <;>
      simp only [Execution.AsyncFootprint] at hF
    · obtain ⟨s, hc, -⟩ := hF
      exact (noCopy hX hc).elim
    · obtain ⟨s, addr, hi, hl, hz⟩ := hF
      exact .inl (.inr (.inr ⟨x, y, k, s, addr, rfl, hi, hl, hz⟩))
    · obtain ⟨s, addr, hi, hl, hz⟩ := hF
      exact .inr (.inl ⟨x, y, k, s, addr, .inl rfl, hi, hl, hz⟩)
    · obtain ⟨s, tg, hi, -⟩ := hF
      exact (noClcIssue hX hi).elim
    · obtain ⟨s, hc, -⟩ := hF
      exact (noCopy hX hc).elim
  · rcases s with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j <;>
      simp only [Execution.AsyncFootprint] at hF
    · obtain ⟨s, addr, hi, -, hl, hz⟩ := hF
      exact .inr (.inl ⟨x, y, k, s, addr, .inr rfl, hi, hl, hz⟩)
    · obtain ⟨s, r, hc, -⟩ := hF
      exact (noCopy hX hc).elim
  all_goals simp only [Execution.AsyncFootprint] at hF
  obtain ⟨hsz, hf⟩ := hF
  exact .inl (.inl ⟨isB, idx, rfl, hsz, hf⟩)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

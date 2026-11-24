-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.Order
public import Lemmas.Async.AsyncCopy
public import Lemmas.Tensor.TensorCopy
public import Lemmas.Order.Order

@[expose] public section

/-! # The accesses of a memory region

A proof tool for the memory regions of a kernel. Every access of an execution, a thread's or an
asynchronous operation's, has a footprint fixed at its issue (`Execution.Intent`); a write is an
access that writes (`Execution.MemWrites.intent`). An access covering a byte of shared memory is a
thread's access, an MMA operand read, a tensor store's read of its source, a tensor load's write of
its destination, a CLC response write of its target CTA's response buffer, or a bulk copy's access
(`shared_intent`): tensor loads read and tensor stores write global memory only. A kernel that
places each of these, by its issuing event, in the regions of its shared window then knows every
accessor of each region. -/

namespace PTX.Execution

open AsyncCopy

variable {X : Execution}

/-- A tensor load reads global memory. -/
theorem tensor_readLoc_global {s : TensorCopy.Spec} {x y k : Nat} {l : Loc}
    (h : TensorCopy.readLoc s x y k = some l) : l.space = .global :=
  TensorTransfer.sourceLoc_global h

/-- A tensor store writes global memory. -/
theorem store_writeLoc_global {s : TensorStore.Spec} {x y k : Nat} {l : Loc}
    (h : TensorStore.writeLoc s x y k = some l) : l.space = .global := by
  unfold TensorStore.writeLoc TensorStore.destination at h
  cases hs : TensorTransfer.slotAt s.descriptor x y k with
  | none => simp [hs] at h
  | some slot =>
    simp only [hs, Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl

/-- **The accessors of shared memory.** An access covering a shared byte is a thread's access, an
MMA operand read, a tensor store's read, a tensor load's write, a CLC response write of a target's
response buffer, a stage of a linear copy, or a bulk prefetch's source read. -/
theorem shared_intent {ref : Ref} {a : Acc} {w : Bool} {l : Loc} (h : X.Intent ref a w)
    (hc : a.Covers l) (hs : l.space = .shared) :
    (∃ e, ref = .thread e ∧ X.Access e a w) ∨
    (∃ i isB idx, ref = .async i (.mmaRead isB idx)) ∨
    (∃ i x y k, ref = .async i (.read (.store x y k))) ∨
    (∃ i x y k, ref = .async i (.write (.load x y k))) ∨
    (∃ i c s tg, ref = .async i (.write (.cta c)) ∧ X.ClcIssue i s tg ∧ c ∈ tg ∧
      a = { loc := { s.response with cta := c }, size := 16 }) ∨
    (∃ i q s, ref = .async i q ∧ X.Copy i s) ∨
    (∃ i, ref = .async i (.read .copy) ∧ X.BulkPrefetch i a) := by
  have hsp : a.loc.space = .shared := hc.1.symm.trans hs
  rcases ref with e | ⟨i, p⟩
  · exact .inl ⟨e, rfl, h⟩
  cases p with
  | mmaRead isB idx => exact .inr (.inl ⟨i, isB, idx, rfl⟩)
  | readStore x y k => exact .inr (.inr (.inl ⟨i, x, y, k, rfl⟩))
  | writeLoad x y k => exact .inr (.inr (.inr (.inl ⟨i, x, y, k, rfl⟩)))
  | writeCta c =>
    obtain ⟨-, s, tg, hi, hm, ha⟩ := h
    exact .inr (.inr (.inr (.inr (.inl ⟨i, c, s, tg, rfl, hi, hm, ha⟩))))
  | readCopy =>
    obtain ⟨-, hsrc | hpf⟩ := h
    · obtain ⟨s, hc, -⟩ := hsrc
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨i, _, s, rfl, hc⟩)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨i, rfl, hpf⟩)))))
  | writeCopy =>
    obtain ⟨-, s, hc, -, -⟩ := h
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨i, _, s, rfl, hc⟩)))))
  | writeElem j =>
    obtain ⟨-, s, hc, -⟩ := h
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨i, _, s, rfl, hc⟩)))))
  | oldElem j =>
    obtain ⟨-, s, -, hc, -⟩ := h
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨i, _, s, rfl, hc⟩)))))
  | readLoad x y k =>
    obtain ⟨-, s, addr, -, hl, -⟩ := h
    rw [tensor_readLoc_global hl] at hsp
    cases hsp
  | writeStore x y k =>
    obtain ⟨-, s, addr, -, hl, -⟩ := h
    rw [store_writeLoc_global hl] at hsp
    cases hsp
  | readPrefetch x y k =>
    obtain ⟨-, s, addr, -, hl, -⟩ := h
    rw [TensorTransfer.sourceLoc_global hl] at hsp
    cases hsp
  | oldStore x y k =>
    obtain ⟨-, s, addr, -, -, hl, -⟩ := h
    rw [store_writeLoc_global hl] at hsp
    cases hsp
  | _ => exact h.2.elim

end PTX.Execution

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.VoteInv

@[expose] public section

/-! # The data machine when the role is entered

The events of the startup (pcs below 103) are no loads the block loop reads: the words of the
block in progress are the empty ones, so the initial data state holds the trace invariant for the
whole startup prefix. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem w0Scan_pre {l : List Event} (h : ∀ f ∈ l, f.pc < 103) : w0Scan l = ([], l) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    have h1 := ih (fun f hf => h f (List.mem_append_left _ hf))
    have h2 : e.pc < 103 := h e (by simp)
    rw [w0Scan_snoc, h1]
    simp only [show ¬ (e.pc = w0ArrSPc) by unfold w0ArrSPc; omega, ite_false]

theorem w0Words_pre {l : List Event} (h : ∀ f ∈ l, f.pc < 103) : w0Words l = w0Words [] := by
  have hl : ∀ pcs : List Nat, (∀ p ∈ pcs, 103 ≤ p) → ∀ {α : Type} (f : Event → Option α),
      w0Last f pcs l = none := by
    intro pcs hp α f
    unfold w0Last
    have : l.filterMap (fun e => if e.pc ∈ pcs then f e else none) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro e he
      have := h e he
      simp only [show ¬ (e.pc ∈ pcs) from fun hm => by have := hp _ hm; omega, ite_false]
    rw [this]; rfl
  have hpf : ∀ k, (l.filter fun e => e.pc = 477 + 5 * k && (w0RdVal e).isSome) = [] := by
    intro k
    rw [List.filter_eq_nil_iff]
    intro e he
    have := h e he
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h'; omega
  unfold w0Words
  simp only [hl [280, 283] (by simp) _, hl [278, 285] (by simp) _, hl [289] (by simp) _,
    hl [572] (by simp) _, hl [578] (by simp) _]
  simp only [w0Last, List.filterMap_nil, List.getLast?_nil, Option.getD_none]
  congr 1
  funext k
  simp [w0Peer, hpf k]

theorem invW_pre {l : List Event} (h : ∀ f ∈ l, f.pc < 103) :
    InvW l (code P L g w).init := by
  have hs : (code P L g w).init.c.site = .smr := rfl
  have hpf : ∀ k, w0Pf l k = [] := by
    intro k
    unfold w0Pf
    rw [List.filter_eq_nil_iff]
    intro e he
    have := h e he
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h'; omega
  have hw : w0Words (w0Scan l).2 = w0Words [] := by rw [w0Scan_pre h]; exact w0Words_pre h
  refine ⟨?_, ?_, ?_, fun j => ?_, ?_, ?_, fun k => ?_, fun k h _ => ?_⟩
  all_goals try (rw [hw, w0Words_nil])
  · rw [w0Scan_pre h]
    simp [hpf]
  · rw [hs] at h; cases h

theorem site_pc_ost {s : Site} {j : Nat} (hj : j < 4) (h : s.pc = 704 + j) :
    s = .ost ⟨j, hj⟩ := by
  by_cases hs : ∃ k, s = .ost k
  · obtain ⟨k, rfl⟩ := hs
    have hk := k.isLt
    simp only [Site.pc] at h
    exact congrArg Site.ost (Fin.ext (by simp only; omega))
  · exfalso
    cases s
    all_goals first
      | exact absurd ⟨_, rfl⟩ hs
      | (simp only [Site.pc] at h; omega)
      | (rename_i k; fin_cases k <;> (simp [Site.pc] at h; omega))
      | (rename_i a k; fin_cases a <;> fin_cases k <;> (simp [Site.pc, ost2Base] at h; omega))

theorem holds_of_mem {R : Nat → Option Value} {F : List (Nat × Value)} {r : Nat}
    (h : Holds R F) (hr : r ∈ F.map Prod.fst) : R r = some (lookupD F r) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem hr)
  have := lookup_holds h hv
  unfold lookupD
  rw [hv]
  exact this

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # A block's loads before the row-maximum exchange are final

Events of a block at the pcs 566 to 578 (the row-maximum exchange, its barriers, the vote) add
to the block's events but change none of the words its loads before the exchange read: the
tensor loads, the mask word and the peer pairs (`w0Words_ext`). The block in progress after such
events is the block before them with the events appended (`w0Fin_ext`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

theorem w0Last_ext {α : Type} (f : Event → Option α) (pcs : List Nat) (seg ex : List Event)
    (h : ∀ e ∈ ex, e.pc ∉ pcs) : w0Last f pcs (seg ++ ex) = w0Last f pcs seg := by
  unfold w0Last
  rw [List.filterMap_append]
  have : ex.filterMap (fun e => if e.pc ∈ pcs then f e else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e he
    simp [h e he]
  rw [this, List.append_nil]

theorem w0Peer_ext (seg ex : List Event) (h : ∀ e ∈ ex, 566 ≤ e.pc) {k : Nat} (hk : k < 8) :
    w0Peer (seg ++ ex) k = w0Peer seg k := by
  have hf : ex.filter (fun e => e.pc = 477 + 5 * k && (w0RdVal e).isSome) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    have := h e he
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h'
    omega
  unfold w0Peer
  rw [List.filter_append, hf, List.append_nil]

/-- **The words of the loads before the exchange** of a block do not change by appending events
at the pcs 566 and above. -/
theorem w0Words_ext (seg ex : List Event) (h : ∀ e ∈ ex, 566 ≤ e.pc) :
    (w0Words (seg ++ ex)).lo = (w0Words seg).lo ∧ (w0Words (seg ++ ex)).hi = (w0Words seg).hi ∧
      (w0Words (seg ++ ex)).mw = (w0Words seg).mw ∧
      ∀ j, (w0Words (seg ++ ex)).pw j = (w0Words seg).pw j := by
  refine ⟨?_, ?_, ?_, fun j => ?_⟩
  · simp only [w0Words]
    rw [w0Last_ext _ _ _ _ (fun e he => by have := h e he; simp; omega)]
  · simp only [w0Words]
    rw [w0Last_ext _ _ _ _ (fun e he => by have := h e he; simp; omega)]
  · simp only [w0Words]
    rw [w0Last_ext _ _ _ _ (fun e he => by have := h e he; simp; omega)]
  · simp only [w0Words]
    by_cases hj : j < 8
    · simp only [hj, ↓reduceIte]
      exact w0Peer_ext seg ex h hj
    · simp [hj]

/-- **The block in progress after events** at pcs other than the arrivals at pcs 200 and 1122 is
the block before them with the events appended; the finished blocks are the same. -/
theorem w0Fin_ext (l ex : List Event) (h : ∀ e ∈ ex, e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc) :
    w0Fin (l ++ ex) = ((w0Fin l).1, (w0Fin l).2 ++ ex) := by
  induction ex using List.reverseRecOn with
  | nil => simp
  | append_singleton ex e ih =>
    have h1 := h e (by simp)
    rw [← List.append_assoc, w0Fin_snoc, ih (fun e' he' => h e' (by simp [he']))]
    simp [h1.1, h1.2]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

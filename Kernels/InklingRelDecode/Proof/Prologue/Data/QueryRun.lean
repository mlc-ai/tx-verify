-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryMove
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Query
import Lemmas.Flow.SegPieces
import Lemmas.Flow.RunFrame
import Lemmas.Flow.DataCompute

@[expose] public section

/-! # The skipped query loads with their moves

A load whose group is off is skipped; the move before it leaves the zero half in its register. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

/-- The zero halves of the loads `lo ≤ k < hi`. -/
def zs (lo hi : Nat) : List (Nat × Value) :=
  ((List.finRange 64).filter fun k => lo ≤ k.val ∧ k.val < hi).map fun k => (qDst k, zeroV)

theorem mem_zs {lo hi : Nat} {x : Nat × Value} :
    x ∈ zs lo hi ↔ ∃ k : Fin 64, lo ≤ k.val ∧ k.val < hi ∧ x = (qDst k, zeroV) := by
  simp only [zs, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨fun ⟨k, ⟨h1, h2⟩, e⟩ => ⟨k, h1, h2, e.symm⟩, fun ⟨k, h1, h2, e⟩ => ⟨k, ⟨h1, h2⟩, e.symm⟩⟩

theorem qDst_inj : ∀ i j : Fin 64, qDst i = qDst j → i = j := by decide +kernel

/-- **The move of the zero half** into the register of the load after `n`. -/
theorem move_next {L g} {S : List (Nat × Value)} (n : Fin 63) (hz : (199, zeroV) ∈ S)
    (hn : qDst ⟨n.val + 1, by omega⟩ ∉ S.map Prod.fst) :
    SegU kernel Assumptions.all L g (queryPc ⟨n.val, by omega⟩ + 1) S
      (queryPc ⟨n.val + 1, by omega⟩) ((qDst ⟨n.val + 1, by omega⟩, zeroV) :: S) := by
  have mv := qmove_step (L := L) (g := g) ⟨n.val + 1, by omega⟩ hz hn
  simp only [queryPc, Site.pc] at *
  rwa [show 388 + 2 * n.val + 1 = 387 + 2 * (n.val + 1) by omega]

/-- **The run over one skipped load and the move of the next**, from the zero half of the
current load's register. -/
theorem skip_step {L g} {S : List (Nat × Value)} (n : Fin 63) (hz : (199, zeroV) ∈ S)
    (hg : (queryPred ⟨n.val, by omega⟩, Value.pred false) ∈ S)
    (hn : qDst ⟨n.val + 1, by omega⟩ ∉ S.map Prod.fst) :
    SegU kernel Assumptions.all L g (queryPc ⟨n.val, by omega⟩) S
      (queryPc ⟨n.val + 1, by omega⟩) ((qDst ⟨n.val + 1, by omega⟩, zeroV) :: S) :=
  (SegU.of_seg (Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
    (qLoadPair (L := L) (g := g) ⟨n.val, by omega⟩).2 hg rfl)).comp (move_next n hz hn)

private theorem skip_nat {L g} {S : List (Nat × Value)} (lo : Fin 64) (hz : (199, zeroV) ∈ S)
    (hfresh : ∀ k : Fin 64, lo < k → qDst k ∉ S.map Prod.fst) :
    ∀ d (hd : lo.val + d < 64),
    (∀ n : Fin 64, lo ≤ n → n.val < lo.val + d → (queryPred n, Value.pred false) ∈ S) →
    SegU kernel Assumptions.all L g (queryPc lo) ((qDst lo, zeroV) :: S)
      (queryPc ⟨lo.val + d, hd⟩) ((qDst lo, zeroV) :: S ++ zs (lo.val + 1) (lo.val + d + 1))
  | 0, hd, _ => by
    intro t ht
    obtain ⟨-, -, -, -, htF⟩ := id ht
    refine .inl ⟨t, .refl, At.mono ht (holds_of_mem fun r v hm => holds_mem htF ?_)⟩
    rcases List.mem_append.mp hm with h | h
    · exact h
    · obtain ⟨k, h1, h2, -⟩ := mem_zs.mp h; omega
  | d + 1, hd, hg => by
    have ih := skip_nat (L := L) (g := g) lo hz hfresh d (by omega)
      fun m h1 h2 => hg m h1 (by omega)
    have stp := skip_step (L := L) (g := g) ⟨lo.val + d, by omega⟩
      (S := (qDst lo, zeroV) :: S ++ zs (lo.val + 1) (lo.val + d + 1))
      (by simp [hz]) (by
        simp only [List.cons_append, List.mem_cons, List.mem_append]
        exact .inr (.inl (hg ⟨lo.val + d, by omega⟩ (by simp [Fin.le_def]) (by simp))))
      (by
        simp only [List.cons_append, List.map_cons, List.map_append, List.mem_cons,
          List.mem_append, not_or]
        refine ⟨fun h => ?_, hfresh _ (by simp [Fin.lt_def]), fun h => ?_⟩
        · have := qDst_inj _ _ h
          simp only [Fin.ext_iff] at this; omega
        · obtain ⟨x, hx, e⟩ := List.mem_map.mp h
          obtain ⟨k, h1, h2, rfl⟩ := mem_zs.mp hx
          have := qDst_inj _ _ e
          simp only [Fin.ext_iff] at this; omega)
    refine SegU.mono_goal (ih.comp stp) fun x hx => ?_
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with h | h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · obtain ⟨k, h1, h2, rfl⟩ := mem_zs.mp h
      by_cases hk : k.val = lo.val + d + 1
      · exact .inl (by rw [show k = ⟨lo.val + d + 1, by omega⟩ from Fin.ext hk])
      · exact .inr (.inr (.inr (mem_zs.mpr ⟨k, h1, by omega, rfl⟩)))

/-- **The skipped loads from `lo` up to `hi`** (`hi` a load), with their moves. -/
theorem skip_data {L g} {S : List (Nat × Value)} (lo hi : Fin 64) (ord : lo ≤ hi)
    (hz : (199, zeroV) ∈ S) (hfresh : ∀ k : Fin 64, lo < k → qDst k ∉ S.map Prod.fst)
    (hg : ∀ n : Fin 64, lo ≤ n → n < hi → (queryPred n, Value.pred false) ∈ S) :
    SegU kernel Assumptions.all L g (queryPc lo) ((qDst lo, zeroV) :: S) (queryPc hi)
      ((qDst lo, zeroV) :: S ++ zs (lo.val + 1) (hi.val + 1)) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show lo.val ≤ hi.val from ord)
  have := skip_nat (L := L) (g := g) lo hz hfresh d (by omega) (fun n h1 h2 => hg n h1 (by
    simp only [Fin.lt_def]; omega))
  have e : hi = ⟨lo.val + d, by omega⟩ := Fin.ext (by simp; omega)
  rw [e]
  simpa [e] using this

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data

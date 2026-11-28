-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryMove
public import Kernels.InklingRelDecode.Proof.Prologue.Data.Carry
public import Lemmas.Flow.SegFrameR
import Lemmas.Flow.DataCompute
import Kernels.InklingRelDecode.Proof.Lib.RulesFrame

@[expose] public section

/-! # The packs of the query words

The four packs before a vector store join eight halves into the four words it writes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section

/-- The packed words `lo ≤ k < hi` of the store `i` from the halves `hv`. -/
def qws (i : Fin 8) (hv : Fin 64 → Value) (lo hi : Nat) : List (Nat × Value) :=
  ((List.finRange 4).filter fun k => lo ≤ k.val ∧ k.val < hi).map fun k =>
    (747 + 5 * i.val + k.val, joinValue (hv (pk i k 0)) (hv (pk i k 1)))

theorem mem_qws {i hv lo hi} {x : Nat × Value} : x ∈ qws i hv lo hi ↔ ∃ k : Fin 4,
    lo ≤ k.val ∧ k.val < hi ∧
      x = (747 + 5 * i.val + k.val, joinValue (hv (pk i k 0)) (hv (pk i k 1))) := by
  simp only [qws, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨fun ⟨k, ⟨h1, h2⟩, e⟩ => ⟨k, h1, h2, e.symm⟩, fun ⟨k, h1, h2, e⟩ => ⟨k, ⟨h1, h2⟩, e.symm⟩⟩

private theorem pack_nat {L g} (i : Fin 8) (hv : Fin 64 → Value) {S : List (Nat × Value)}
    (hx : ∀ k : Fin 4, ∀ b : Fin 2, (qDst (pk i k b), hv (pk i k b)) ∈ S)
    (hfresh : ∀ k : Fin 4, 747 + 5 * i.val + k.val ∉ S.map Prod.fst) :
    ∀ m, m ≤ 4 → SegU kernel Assumptions.all L g (522 + 6 * i.val) S
      (522 + 6 * i.val + m) (qws i hv 0 m ++ S)
  | 0, _ => by
    intro t ht
    obtain ⟨-, -, -, -, htF⟩ := id ht
    exact .inl ⟨t, .refl, At.mono ht (holds_of_mem fun r v hm => holds_mem htF (by
      rcases List.mem_append.mp hm with h | h
      · obtain ⟨k, h1, h2, -⟩ := mem_qws.mp h; omega
      · exact h))⟩
  | m + 1, hm => by
    have ih := pack_nat (L := L) (g := g) i hv hx hfresh m (by omega)
    have stp := pack_step (L := L) (g := g) i ⟨m, by omega⟩ (F := qws i hv 0 m ++ S)
      (List.mem_append_right _ (hx ⟨m, by omega⟩ 0)) (List.mem_append_right _ (hx ⟨m, by omega⟩ 1))
      (by
        simp only [List.map_append, List.mem_append, not_or]
        refine ⟨fun h => ?_, hfresh ⟨m, by omega⟩⟩
        obtain ⟨x, hx', e⟩ := List.mem_map.mp h
        obtain ⟨k, h1, h2, rfl⟩ := mem_qws.mp hx'
        simp only at e; omega)
    refine SegU.mono_goal (ih.comp stp) fun x hx' => ?_
    simp only [List.mem_append, List.mem_cons] at hx' ⊢
    rcases hx' with h | h
    · obtain ⟨k, h1, h2, rfl⟩ := mem_qws.mp h
      by_cases hk : k.val = m
      · exact .inl (by rw [show k = ⟨m, by omega⟩ from Fin.ext hk])
      · exact .inr (.inl (mem_qws.mpr ⟨k, h1, by omega, rfl⟩))
    · exact .inr (.inr h)

/-- **The four packs of the store `i`** join the halves `hv` of its eight loads. -/
theorem pack_tail {L g} (i : Fin 8) (hv : Fin 64 → Value) {S : List (Nat × Value)}
    (hx : ∀ k : Fin 4, ∀ b : Fin 2, (qDst (pk i k b), hv (pk i k b)) ∈ S)
    (hfresh : ∀ k : Fin 4, 747 + 5 * i.val + k.val ∉ S.map Prod.fst) :
    SegU kernel Assumptions.all L g (522 + 6 * i.val) S (526 + 6 * i.val)
      (qws i hv 0 4 ++ S) :=
  by simpa [show 522 + 6 * i.val + 4 = 526 + 6 * i.val by omega] using
    pack_nat (L := L) (g := g) i hv hx hfresh 4 le_rfl

/-- The halves of the loads `lo ≤ k < hi`. -/
def qhf (hv : Fin 64 → Value) (lo hi : Nat) : List (Nat × Value) :=
  ((List.finRange 64).filter fun k => lo ≤ k.val ∧ k.val < hi).map fun k => (qDst k, hv k)

theorem mem_qhf {hv lo hi} {x : Nat × Value} : x ∈ qhf hv lo hi ↔ ∃ k : Fin 64,
    lo ≤ k.val ∧ k.val < hi ∧ x = (qDst k, hv k) := by
  simp only [qhf, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨fun ⟨k, ⟨h1, h2⟩, e⟩ => ⟨k, h1, h2, e.symm⟩, fun ⟨k, h1, h2, e⟩ => ⟨k, ⟨h1, h2⟩, e.symm⟩⟩

theorem qdst_lt : ∀ k : Fin 64, qDst k < 300 := by decide +kernel

theorem qw_nonctl : ∀ (i : Fin 8) (k : Fin 4), Control.ctl (747 + 5 * i.val + k.val) = false := by
  decide +kernel

/-- No instruction from `lo` on writes the register of a load's half. -/
theorem qdst_region {lo : Nat} (h : 514 ≤ lo) (hv : Fin 64 → Value) (a b : Nat) :
    regionB kernel lo 574 ((qhf hv a b).map Prod.fst) = true := by
  have := region_tags (T := (List.finRange 64).map Tag.qh) (lo := lo) (by omega) (fun τ hτ => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hτ
    simp only [Tag.pc]; omega)
  refine regionB_mono this fun r hr => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  obtain ⟨k, -, -, rfl⟩ := mem_qhf.mp hx
  exact List.mem_map.mpr ⟨.qh k, List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩, rfl⟩

/-- **A control segment up to the packs of the store `i`, then the packs**: the eight halves are
facts on both sides of the control part. -/
theorem addr_packs {L g} (i : Fin 8) (hv : Fin 64 → Value) {s : Nat}
    {Fa Fb H : List (Nat × Value)}
    (ctl : SegU kernel Assumptions.all L g s Fa (522 + 6 * i.val) Fb) (hs : 514 ≤ s)
    (hsb : s ≤ 522 + 6 * i.val) (hB : regionB kernel s 574 (H.map Prod.fst) = true)
    (hx : ∀ k : Fin 4, ∀ b : Fin 2, (qDst (pk i k b), hv (pk i k b)) ∈ H)
    (hfresh : ∀ k : Fin 4, 747 + 5 * i.val + k.val ∉ (Fb ++ H).map Prod.fst) :
    SegU kernel Assumptions.all L g s (Fa ++ H) (526 + 6 * i.val) (qws i hv 0 4 ++ (Fb ++ H)) :=
  (SegU.frameR Lib.rulesFrame ctl hB (fun pc h1 h2 => seg_range (by omega) h2) le_rfl
    (by omega)).comp
    (pack_tail i hv (fun k b => List.mem_append_right _ (hx k b)) hfresh)

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data

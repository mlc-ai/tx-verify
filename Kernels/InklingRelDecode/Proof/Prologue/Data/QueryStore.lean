-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryLoad
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryAddr
import Lemmas.Flow.SegPieces

@[expose] public section

/-! # The packs of the query words, after the control run to the store

The address run (control facts only) and the four packs of a vector store, with the halves a
fact on both sides. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

/-- The control facts at the packs do not name the registers of a store's words. -/
theorem packs_fresh {Q L g w} (c : Control.D) (i : Fin 8) (pc : Nat) (hv : Fin 64 → Value)
    (a b : Nat) (k : Fin 4) :
    747 + 5 * i.val + k.val ∉ (facts Q L g w c pc ++ qhf hv a b).map Prod.fst := by
  simp only [List.map_append, List.mem_append, not_or]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Control.facts, factsFrom_keys] at h
    have := (List.mem_filter.mp h).2
    rw [qw_nonctl i k] at this; cases this
  · obtain ⟨x, hx, e⟩ := List.mem_map.mp h
    obtain ⟨k', -, -, rfl⟩ := mem_qhf.mp hx
    have := qdst_lt k'
    simp only at e; omega

/-- **The first store's packs** from the halves of all 64 loads. -/
theorem store_first {Q L g w} (c : Control.D) (hv : Fin 64 → Value) {S : List (Nat × Value)}
    (hS : ∀ x ∈ facts Q L g w c 514, x ∈ S) (hH : ∀ k : Fin 64, (qDst k, hv k) ∈ S) :
    SegU kernel Assumptions.all L g 515 S 526
      (qws 0 hv 0 4 ++ (facts Q L g w c 522 ++ qhf hv 0 64)) := by
  refine SegU.sub_start (addr_packs (0 : Fin 8) hv (Fa := facts Q L g w c 514)
    (Fb := facts Q L g w c 522) (H := qhf hv 0 64) first_addr_522 (by omega) (by omega)
    (qdst_region (by omega) hv 0 64) (fun k b => mem_qhf.mpr ⟨_, by omega, by
      have := (pk 0 k b).isLt; omega, rfl⟩) (fun k => packs_fresh c 0 522 hv 0 64 k)) ?_
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hS x h
  · obtain ⟨k, -, -, rfl⟩ := mem_qhf.mp h
    exact hH k

theorem ctl514 : ∀ j : Fin 64, ∀ r ∈ ctlLive 514, r ∈ ctlLive (queryPc j) := by decide +kernel

/-- **From a load to the first store**, the loads after it skipped. -/
theorem ldq_chain_end {Q L g w} {d d' : D} {j : Fin 64} {v : Value} (hs : d.c.site = .ldq j)
    (hon : queryOn (g % L.block) (j.val / 16) d.c = true)
    (hcc : d'.c = {d.c with site := qSiteAt 64}) (hv : d'.v = ⟨d.v.pay, Function.update d.v.q j v⟩)
    (hoff : ∀ n, j.val < n → n < 64 → queryOn (g % L.block) (n / 16) d.c = false) :
    ∃ S, (∀ x ∈ ldqF Q L g w d j v, x ∈ S) ∧ (∀ k : Fin 64, (qDst k, qv L g d' k) ∈ S) ∧
      SegU kernel Assumptions.all L g ((Site.ldq j).pc + 1) (ldqF Q L g w d j v) 515 S := by
  have hq : ∀ n, queryOn (g % L.block) n d'.c = queryOn (g % L.block) n d.c := fun n => by
    rw [hcc]; rfl
  have hz := ldq_zero hs (Q := Q) (L := L) (g := g) (w := w) (v := v)
  by_cases hj : j.val = 63
  · refine ⟨_, fun _ h => h, fun k => ldq_half (Q := Q) (w := w) hs hon hcc hv k ?_, ?_⟩
    · exact Fin.le_def.mpr (by have := k.isLt; omega)
    · intro t ht
      refine .inl ⟨t, .refl, ?_⟩
      simpa [Site.pc, hj] using ht
  · have hj63 : j.val < 63 := by have := j.isLt; omega
    have lt1 : (⟨j.val, by omega⟩ : Fin 64) < ⟨j.val + 1, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have m1 := move_next (L := L) (g := g) (S := ldqF Q L g w d j v) ⟨j.val, hj63⟩ hz
      (ldqF_fresh hs ⟨j.val + 1, by omega⟩ lt1)
    have sk := skip_data (L := L) (g := g) (S := ldqF Q L g w d j v) ⟨j.val + 1, by omega⟩
      ⟨63, by omega⟩ (Fin.mk_le_mk.mpr (by omega)) hz
      (fun k hk => ldqF_fresh hs k
        (Fin.lt_def.mpr (by have := Fin.lt_def.mp hk; simp at this; omega)))
      (fun n h1 h2 => guard_mem hs
        (Fin.lt_def.mpr (by have := Fin.le_def.mp h1; simp at this; omega))
        (hoff n (by have := Fin.le_def.mp h1; simp at this; omega)
          (by have := Fin.lt_def.mp h2; simp at this; omega)))
    have hg63 : (queryPred ⟨63, by omega⟩, Value.pred false) ∈
        (qDst ⟨j.val + 1, by omega⟩, zeroV) :: ldqF Q L g w d j v ++ zs (j.val + 1 + 1) (63 + 1) :=
      List.mem_append_left _ (List.mem_cons_of_mem _ (guard_mem hs
        (Fin.lt_def.mpr (by simp; omega)) (hoff 63 (by omega) (by omega))))
    have last := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
      (qLoadPair (L := L) (g := g) ⟨63, by omega⟩).2 hg63 rfl
    refine ⟨_, fun x hx => List.mem_append_left _ (List.mem_cons_of_mem _ hx), fun k => ?_,
      m1.comp (sk.comp (SegU.of_seg last))⟩
    by_cases hkj : k ≤ j
    · exact List.mem_append_left _ (List.mem_cons_of_mem _
        (ldq_half (Q := Q) (w := w) hs hon hcc hv k hkj))
    · have hkj' : j.val < k.val := Fin.lt_def.mp (not_le.mp hkj)
      have hz' : qv L g d' k = zeroV := qv_off (by rw [hq]; exact hoff k hkj' (by omega))
      rw [hz']
      by_cases hk1 : k.val = j.val + 1
      · exact List.mem_append_left _ (by
          rw [show k = ⟨j.val + 1, by omega⟩ from Fin.ext hk1]; exact List.mem_cons_self ..)
      · exact List.mem_append_right _ (mem_zs.mpr ⟨k, by omega, by omega, rfl⟩)

theorem stq_tags (i : Fin 8) (j : Fin 4) : ∀ τ ∈ tags (.stq i j), τ = .scale ∨
    (∃ k : Fin 4, j ≤ k ∧ τ = .qw i k) ∨ ∃ k : Fin 64, 8 * (i.val + 1) ≤ k.val ∧ τ = .qh k := by
  intro τ hτ
  simp only [tags, oldTags, pos, early, qTags, qhs, List.mem_append, List.mem_cons,
    List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    List.not_mem_nil, or_false, Bool.false_eq_true, ↓reduceIte] at hτ
  rcases hτ with h | ⟨k, hk, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩
  · exact .inl h
  · exact .inr (.inl ⟨k, Fin.le_def.mpr hk, rfl⟩)
  · exact .inr (.inr ⟨k, hk, rfl⟩)

/-- **The facts of the first store** from a run that ends before its address with the halves of
all loads. -/
theorem reach_first_store {Q L g w} (d' : D) (c : Control.D) {p : Nat} {F S : List (Nat × Value)}
    (hd' : d'.c.site = .stq 0 0) (hscale : (525, scaleVal L) ∈ F) (hp : 27 ≤ p) (hp5 : p ≤ 526)
    (hS : ∀ x ∈ facts Q L g w c 514, x ∈ S) (hall : ∀ k : Fin 64, (qDst k, qv L g d' k) ∈ S)
    (hseg : SegU kernel Assumptions.all L g p F 515 S) :
    Reach kernel Assumptions.all L g p F (dF Q L g d') := by
  refine reach_tags d' (by rw [hd']; rfl) hp hp5 (by omega)
    (hseg.comp (store_first c (qv L g d') hS hall)) fun τ hτ => ?_
  rw [hd'] at hτ
  rcases stq_tags 0 0 τ hτ with rfl | ⟨k, -, rfl⟩ | ⟨k, hk, rfl⟩
  · exact .inl ⟨hscale, by simp [Tag.pc]; omega⟩
  · exact .inr (List.mem_append_left _ (mem_qws.mpr ⟨k, by omega, by omega,
      Prod.ext (by simp [Tag.reg]) (by simp [Tag.val, pk])⟩))
  · exact .inr (List.mem_append_right _ (List.mem_append_right _
      (mem_qhf.mpr ⟨k, by omega, k.isLt, rfl⟩)))

/-- **The facts of the first store after a load**, the loads after it skipped. -/
theorem ldq_reach_end {Q L g w} {d d' : D} {j : Fin 64} {v : Value} (hs : d.c.site = .ldq j)
    (hon : queryOn (g % L.block) (j.val / 16) d.c = true)
    (hcc : d'.c = {d.c with site := qSiteAt 64}) (hv : d'.v = ⟨d.v.pay, Function.update d.v.q j v⟩)
    (hoff : ∀ n, j.val < n → n < 64 → queryOn (g % L.block) (n / 16) d.c = false) :
    Reach kernel Assumptions.all L g ((Site.ldq j).pc + 1) (ldqF Q L g w d j v) (dF Q L g d') := by
  obtain ⟨S, hFS, hall, hseg⟩ := ldq_chain_end (w := w) hs hon hcc hv hoff
  have := j.isLt
  refine reach_first_store (w := w) d' d.c (by rw [hcc]; rfl)
    (List.mem_append_left _ (List.mem_append_right _ (mem_dF (hs ▸ (ldq_mem j).1))))
    (by simp [Site.pc]; omega) (by simp [Site.pc]; omega) (fun x hx => ?_) hall hseg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (by simpa [Control.facts, factsFrom] using hx)
  refine hFS _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  have : r ∈ ctlLive d.c.site.pc := by rw [hs]; exact ctl514 j r hr
  exact mem_factsFrom (val := valueOf Q L g w d.c) this

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data

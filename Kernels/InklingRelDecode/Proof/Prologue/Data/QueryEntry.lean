-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryStore
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryStart

import Lemmas.Flow.SegPieces

@[expose] public section

/-! # The facts of the first query site

From the end of the copy tail the control run reaches the two moves of the loads; the zero half
and the moves of the groups that are off leave the zero halves of the loads before the first
site.-/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

theorem ctl386 : (199 ∉ ctlLive 386 ∧ ∀ k : Fin 64, qDst k ≠ 199 ∧ qDst k ∉ ctlLive 386) ∧
    (∀ n : Fin 64, queryPred n ∈ ctlLive 386) ∧ ∀ r ∈ ctlLive 514, r = 199 ∨ r ∈ ctlLive 386 := by
  decide +kernel

/-- **The run from the zero half to the first load**, the loads before it skipped. -/
theorem entry_chain {Q L g w} (c : Control.D) (hi : Fin 64)
    (hoff : ∀ n : Fin 64, n < hi → queryOn (g % L.block) (n.val / 16) c = false) :
    ∃ G0, (199, zeroV) ∈ G0 ∧ (∀ k : Fin 64, k < hi → (qDst k, zeroV) ∈ G0) ∧
      SegU kernel Assumptions.all L g 386 (facts Q L g w c 386) (queryPc hi) G0 := by
  obtain ⟨⟨h199, hk⟩, hp, -⟩ := ctl386
  have hn : 199 ∉ (facts Q L g w c 386).map Prod.fst := by
    rw [Control.facts, factsFrom_keys]; exact h199
  have z0 := zero_step (L := L) (g := g) hn
  have hz : (199, zeroV) ∈ (199, zeroV) :: facts Q L g w c 386 := List.mem_cons_self ..
  have hkey : ∀ k : Fin 64, qDst k ∉ ((199, zeroV) :: facts Q L g w c 386).map Prod.fst := by
    intro k
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨(hk k).1, by rw [Control.facts, factsFrom_keys]; exact (hk k).2⟩
  have m0 := qmove_step (L := L) (g := g) (0 : Fin 64) hz (hkey 0)
  have sk := skip_data (L := L) (g := g) (S := (199, zeroV) :: facts Q L g w c 386) 0 hi
    (Fin.zero_le _) hz (fun k _ => hkey k) (fun n _ h2 => by
      refine List.mem_cons_of_mem _ (mem_factsFrom_eq (v := valueOf Q L g w c) (hp n) ?_)
      rw [query_value, hoff n h2])
  refine ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ hz), fun k hk => ?_,
    z0.comp (m0.comp sk)⟩
  by_cases h0 : k = 0
  · subst h0; exact List.mem_append_left _ (List.mem_cons_self ..)
  · exact List.mem_append_right _ (mem_zs.mpr ⟨k, by
      have := Fin.pos_iff_ne_zero.mpr h0; exact this, by have := Fin.lt_def.mp hk; omega, rfl⟩)

/-- **The run from the zero half past all loads**, every group off. -/
theorem entry_chain_end {Q L g w} (c : Control.D)
    (hoff : ∀ n : Fin 64, queryOn (g % L.block) (n.val / 16) c = false) :
    ∃ S, (∀ x ∈ facts Q L g w c 514, x ∈ S) ∧ (∀ k : Fin 64, (qDst k, zeroV) ∈ S) ∧
      SegU kernel Assumptions.all L g 386 (facts Q L g w c 386) 515 S := by
  obtain ⟨⟨h199, hk⟩, hp, h514⟩ := ctl386
  have hn : 199 ∉ (facts Q L g w c 386).map Prod.fst := by
    rw [Control.facts, factsFrom_keys]; exact h199
  have z0 := zero_step (L := L) (g := g) hn
  have hz : (199, zeroV) ∈ (199, zeroV) :: facts Q L g w c 386 := List.mem_cons_self ..
  have hkey : ∀ k : Fin 64, qDst k ∉ ((199, zeroV) :: facts Q L g w c 386).map Prod.fst := by
    intro k
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨(hk k).1, by rw [Control.facts, factsFrom_keys]; exact (hk k).2⟩
  have hg : ∀ n : Fin 64, (queryPred n, Value.pred false) ∈
      (199, zeroV) :: facts Q L g w c 386 := fun n => by
    refine List.mem_cons_of_mem _ (mem_factsFrom_eq (v := valueOf Q L g w c) (hp n) ?_)
    rw [query_value, hoff n]
  have m0 := qmove_step (L := L) (g := g) (0 : Fin 64) hz (hkey 0)
  have sk := skip_data (L := L) (g := g) (S := (199, zeroV) :: facts Q L g w c 386) 0 ⟨63, by omega⟩
    (Fin.zero_le _) hz (fun k _ => hkey k) (fun n _ _ => hg n)
  have hg63 : (queryPred ⟨63, by omega⟩, Value.pred false) ∈ (qDst 0, zeroV) :: (199, zeroV) ::
      facts Q L g w c 386 ++ zs (0 + 1) (63 + 1) :=
    List.mem_append_left _ (List.mem_cons_of_mem _ (hg ⟨63, by omega⟩))
  have last := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
    (qLoadPair (L := L) (g := g) ⟨63, by omega⟩).2 hg63 rfl
  refine ⟨_, fun x hx => ?_, fun k => ?_, z0.comp (m0.comp (sk.comp (SegU.of_seg last)))⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (by simpa [Control.facts, factsFrom] using hx)
    rcases h514 r hr with rfl | hr'
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (mem_factsFrom (val := valueOf Q L g w c) hr')))
  · by_cases h0 : k = 0
    · subst h0; exact List.mem_append_left _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (mem_zs.mpr ⟨k, by
        have := Fin.pos_iff_ne_zero.mpr h0; exact this, by have := k.isLt; omega, rfl⟩)

/-- **The facts of the first query site** from the end of the copy tail. -/
theorem entry_reach {Q L g w m} (hp : Pre Q L m) (c : Control.D) (d' : D) {p : Nat}
    {F : List (Nat × Value)} (hseg : SegU kernel Assumptions.all L g p F 316 (facts Q L g w c 316))
    (hsite : d'.c.site = querySite (g % L.block) c 0)
    (hq : ∀ n, queryOn (g % L.block) n d'.c = queryOn (g % L.block) n c)
    (hscale : (525, scaleVal L) ∈ F) (hp27 : 27 ≤ p) (hp316 : p ≤ 316) :
    Reach kernel Assumptions.all L g p F (dF Q L g d') := by
  obtain ⟨hi, h64, -, hsite', hoff, hon⟩ := querySite_spec (g % L.block) c 0 (by omega)
  have hseg' := hseg.comp (query_start_386 (w := w) hp)
  by_cases hlt : hi < 64
  · have hd' : d'.c.site = .ldq ⟨hi, hlt⟩ := by rw [hsite, hsite']; simp [qSiteAt, hlt]
    obtain ⟨G0, hz0, hG0, hrun⟩ := entry_chain (Q := Q) (w := w) c ⟨hi, hlt⟩ (fun n hn =>
      hoff n (by omega) (Fin.lt_def.mp hn))
    refine reach_tags d' (by rw [hd']; rfl) hp27 (by simp [queryPc, Site.pc]; omega)
      (by simp [queryPc, Site.pc]; omega) (hseg'.comp hrun) fun τ hτ => ?_
    rw [hd'] at hτ
    rcases ldq_tags ⟨hi, hlt⟩ τ hτ with rfl | rfl | ⟨k, hk, rfl⟩
    · exact .inl ⟨hscale, by simp [Tag.pc]; omega⟩
    · exact .inr hz0
    · have := hG0 k hk
      rw [Tag.val, qv_off (by rw [hq]; exact hoff k (by omega) (by simpa [Fin.lt_def] using hk))]
      exact .inr this
  · have hd' : d'.c.site = .stq 0 0 := by
      rw [hsite, hsite']; have : hi = 64 := by omega
      subst this; rfl
    obtain ⟨S, hS, hall, hrun⟩ := entry_chain_end (Q := Q) (w := w) c fun n => hoff n (by omega) (by
      have := n.isLt; omega)
    exact reach_first_store d' c hd' hscale hp27 (by omega) hS (fun k => by
      rw [qv_off (by rw [hq]; exact hoff k (by omega) (by have := k.isLt; omega))]
      exact hall k) (hseg'.comp hrun)

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data

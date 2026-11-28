-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryElect
public import Lemmas.Flow.DataStoreR

@[expose] public section

/-! # The last element of a vector store: the data step

After the fourth element of the store `i` the packs of the next store run, or the prologue ends. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

theorem stq_fetch : ∀ i : Fin 8, ∃ a, kernel.code[(Site.stq i 3).pc]? = some ⟨none, .mem a⟩ ∧
    a.kind = .store ∧ a.srcs.length = 4 ∧ (Op.mem a).isLocal = false := by
  intro i
  fin_cases i
  · exact ⟨_, Flow.code_526, rfl, rfl, rfl⟩
  · exact ⟨_, Flow.code_532, rfl, rfl, rfl⟩
  · exact ⟨_, Flow.code_538, rfl, rfl, rfl⟩
  · exact ⟨_, Flow.code_544, rfl, rfl, rfl⟩
  · exact ⟨_, Flow.code_550, rfl, rfl, rfl⟩
  · exact ⟨_, Flow.code_556, rfl, rfl, rfl⟩
  · exact ⟨_, Flow.code_562, rfl, rfl, rfl⟩
  · exact ⟨_, Flow.code_568, rfl, rfl, rfl⟩

/-- **The packs of the next store** after the fourth element of store `i`. -/
theorem stq_next_run {Q L g w} (c : Control.D) (i : Fin 8) (hi : i.val + 1 < 8)
    (hv : Fin 64 → Value) {S : List (Nat × Value)}
    (hF : ∀ x ∈ Control.facts Q L g w c (526 + 6 * i.val), x ∈ S)
    (hH : ∀ k : Fin 64, 8 * (i.val + 1) ≤ k.val → k.val < 8 * (i.val + 1) + 8 →
      (qDst k, hv k) ∈ S) :
    SegU kernel Assumptions.all L g (527 + 6 * i.val) S (526 + 6 * (i.val + 1))
      (qws ⟨i.val + 1, hi⟩ hv 0 4 ++ (Control.facts Q L g w c (528 + 6 * i.val) ++
        qhf hv (8 * (i.val + 1)) (8 * (i.val + 1) + 8))) := by
  have ctl : SegU kernel Assumptions.all L g (527 + 6 * i.val)
      (Control.facts Q L g w c (526 + 6 * i.val)) (522 + 6 * (i.val + 1))
      (Control.facts Q L g w c (528 + 6 * i.val)) := by
    have := next_addr_528 (Q := Q) (L := L) (g := g) (w := w) (d := c) ⟨i.val, by omega⟩
    rw [show 522 + 6 * (i.val + 1) = 528 + 6 * i.val by omega]
    exact this
  refine SegU.sub_start (addr_packs (⟨i.val + 1, hi⟩ : Fin 8) hv ctl (by omega) (by simp; omega)
    (qdst_region (by omega) hv _ _) (fun k b => mem_qhf.mpr ⟨pk _ k b, by simp [pk]; omega,
      by simp [pk]; omega, rfl⟩) (fun k => packs_fresh c _ _ hv _ _ k)) ?_
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hF x h
  · obtain ⟨k, h1, h2, rfl⟩ := mem_qhf.mp h
    exact hH k h1 h2

theorem stq_mem : ∀ (i : Fin 8) (j : Fin 4), Tag.scale ∈ tags (.stq i j) ∧
    ∀ k : Fin 64, 8 * (i.val + 1) ≤ k.val → Tag.qh k ∈ tags (.stq i j) := by decide +kernel

/-- **The facts of the next store** after the fourth element of store `i`. -/
theorem stq3_reach {Q L g w} {d d' : D} (i : Fin 8) (hi : i.val + 1 < 8)
    (hs : d.c.site = .stq i 3) (hd' : d'.c.site = .stq ⟨i.val + 1, hi⟩ 0)
    (hq : ∀ k, qv L g d' k = qv L g d k) :
    Reach kernel Assumptions.all L g ((Site.stq i 3).pc + 1)
      ((checkedCode Q L g w).facts d.c ++ dF Q L g d) (dF Q L g d') := by
  have hmem : ∀ k : Fin 64, 8 * (i.val + 1) ≤ k.val → (qDst k, qv L g d' k) ∈ dF Q L g d := by
    intro k hk
    rw [hq]
    exact mem_dF (τ := .qh k) (Q := Q) (L := L) (g := g) (d := d) (hs ▸ (stq_mem i 3).2 k hk)
  have hscale : (525, scaleVal L) ∈ dF Q L g d := scale_dF d (hs ▸ (stq_mem i 3).1)
  have hk64 := fun k : Fin 64 => k.isLt
  rw [show (Site.stq i 3).pc + 1 = 527 + 6 * i.val by simp [Site.pc]; omega]
  refine reach_tags d' (by rw [hd']; rfl) (by omega) (by omega)
    (by omega)
    (stq_next_run d.c i hi (qv L g d') (S := (checkedCode Q L g w).facts d.c ++ dF Q L g d)
      (fun x hx => List.mem_append_left _ (by
        show x ∈ Control.facts Q L g w d.c d.c.site.pc; rw [hs]; exact hx))
      (fun k h1 _ => List.mem_append_right _ (hmem k h1))) fun τ hτ => ?_
  rw [hd'] at hτ
  rcases stq_tags ⟨i.val + 1, hi⟩ 0 τ hτ with rfl | ⟨k, -, rfl⟩ | ⟨k, hk, rfl⟩
  · exact .inl ⟨List.mem_append_right _ hscale, by simp [Tag.pc]⟩
  · exact .inr (List.mem_append_left _ (mem_qws.mpr ⟨k, by omega, by omega,
      Prod.ext (by simp [Tag.reg]) (by simp [Tag.val, pk])⟩))
  · exact .inl ⟨List.mem_append_right _ (hmem k (by simp at hk; omega)), by
      have := hk64 k; simp [Tag.pc]; omega⟩

theorem stq7_tags : ∀ τ ∈ tags .fnc1, τ ∈ tags (.stq 7 3) := by decide +kernel

theorem stq3_step {Q L g w} (d : D) (i : Fin 8) (hs : d.c.site = .stq i 3) :
    DataStep (code Q L g w) (dF Q L g) d := by
  obtain ⟨a, hcode, hk, hlen, hl⟩ := stq_fetch i
  have hc : kernel.code[(code Q L g w).pc d]? = some ⟨none, .mem a⟩ := by
    show kernel.code[d.c.site.pc]? = _
    rw [hs]; exact hcode
  have hpc : (code Q L g w).pc d = (Site.stq i 3).pc := by show d.c.site.pc = _; rw [hs]
  apply DataStep.storeR (C' := code Q L g w) hc hl hk rfl
  · intro h
    exfalso
    have h' : d.c.site.sub + 1 < a.srcs.length := h
    rw [hs, hlen] at h'
    simp [Site.sub] at h'
  · intro e d' hn _
    obtain ⟨c, hnc, rfl⟩ := succ_split hn
    simp only [Control.next, hs, Option.some.injEq] at hnc
    have hrec : record d e = d.v := record_keep (fun b' h' e' => by rw [hs] at e'; cases e')
      (fun j e' => by rw [hs] at e'; cases e')
    rw [hpc]
    show Reach kernel Assumptions.all L g _ ((checkedCode Q L g w).facts d.c ++ dF Q L g d) _
    by_cases hi : i.val + 1 < 8
    · have hd' : c.site = .stq ⟨i.val + 1, hi⟩ 0 := by rw [← hnc]; simp [Control.afterStore, hi]
      exact stq3_reach (d' := ⟨c, record d e⟩) i hi hs hd' (fun k => by
        subst hnc; simp only [qv, hrec]; rfl)
    · have hi7 : i = 7 := by omega
      subst hi7
      have hd' : c.site = .fnc1 := by rw [← hnc]; simp [Control.afterStore]
      refine reach_carry (d := d) (d' := ⟨c, record d e⟩) (fun τ hτ => ?_) ?_
        (by rw [hs]; omega) (by simp [Site.pc]) (by simp [Site.pc])
      · exact hs ▸ stq7_tags τ (hd' ▸ hτ)
      · intro x hx
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp (by simpa [dF] using hx)
        have := (hd' ▸ hτ : τ ∈ tags .fnc1)
        have hsc : τ = .scale := by simpa [tags, oldTags, pos, early, qTags] using this
        subst hsc
        exact List.mem_append_right _ (scale_dF d (hs ▸ (stq_mem 7 3).1))

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data

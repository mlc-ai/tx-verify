-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiSteps0
public import Kernels.InklingRelDecode.Proof.Thread.EpiMul

@[expose] public section

/-! # The packs and products after the Tensor Memory wait

After `tcgen05.wait::ld` (pc 2608) the code packs the 64 loaded words into 32 pairs (pcs
2609-2640), packs the pair `(inv_l, inv_l)` (pc 2641) and multiplies each pair by it (pcs
2642-2673). `pm_run`: when every word is a four-byte value and no product faults (`D.loadOk`),
65 local steps reach pc 2674 with the product pairs `rd2480 + q` valued as `D.prod q`; otherwise
the thread is dead. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {t : TState}

theorem packsAll_code : packCodeB kernel 2609 packsAll = true := by decide +kernel

theorem mulsAll_code : mulCodeCB kernel 2378 2642 mulsAll = true := by decide +kernel

theorem packsAll_nodup : (packsAll.map Prod.fst).Nodup := by decide +kernel

theorem mulsAll_nodup : (mulsAll.map Prod.fst).Nodup := by decide +kernel

theorem packsAll_live : ∀ p ∈ packsAll, p.2.1 ∈ Flow.live 2608 ∧ p.2.2 ∈ Flow.live 2608 := by
  decide +kernel

theorem packsAll_dis : ∀ p ∈ packsAll, ∀ q ∈ packsAll, q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2 := by
  decide +kernel

theorem mulsAll_dis : ∀ m ∈ mulsAll, m.1 ≠ 2378 ∧ ∀ m' ∈ mulsAll, m.1 ≠ m'.2 := by
  decide +kernel

/-- Every live register at pc 2674 is a product, or was live at the wait and written by no pack
or multiplication. -/
theorem pm_cover : ∀ r ∈ Flow.live 2674, (2479 ≤ r ∧ r < 2511) ∨
    (r ∈ Flow.live 2608 ∧ (∀ p ∈ packsAll, p.1 ≠ r) ∧ (∀ m ∈ mulsAll, m.1 ≠ r)) := by
  decide +kernel

theorem mem_packsAll (q : Nat) (hq : q < 32) :
    (2346 + q, 1763 + 2 * q, 1764 + 2 * q) ∈ packsAll := by
  simp only [packsAll, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  exact Or.inl ⟨q, hq, rfl⟩

theorem mem_packsAll_c : (2378, 1761, 1761) ∈ packsAll := by
  simp [packsAll]

theorem mem_mulsAll (q : Nat) (hq : q < 32) : (2479 + q, 2346 + q) ∈ mulsAll := by
  simp only [mulsAll, List.mem_map, List.mem_range]
  exact ⟨31 - q, by omega, by simp only [Prod.mk.injEq]; omega⟩

theorem mulsAll_src (m : Nat × Nat) (hm : m ∈ mulsAll) : ∃ q < 32, m = (2479 + q, 2346 + q) := by
  simp only [mulsAll, List.mem_map, List.mem_range] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  exact ⟨31 - j, by omega, by simp only [Prod.mk.injEq]; omega⟩

theorem packsAll_len : packsAll.length = 33 := by decide +kernel

theorem mulsAll_len : mulsAll.length = 32 := by decide +kernel

/-- **The packs and products.** -/
theorem pm_run (d : D) (hsk : d.sk = false) (h : At t 2609 (factsAt 2608 d)) :
    (d.loadOk = true → ∃ t', run kernel asms L g 65 t = some t' ∧ At t' 2674 (factsAt 2674 d)) ∧
    (d.loadOk = false → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hR := h.2.2.2.2
  set v : Nat → Value := valueOf d with hv
  have hsrc : ∀ p ∈ packsAll, t.regs p.2.1 = some (v p.2.1) ∧ t.regs p.2.2 = some (v p.2.2) :=
    fun p hp => ⟨reg_of hR (packsAll_live p hp).1, reg_of hR (packsAll_live p hp).2⟩
  have hpc : PackCode kernel t.pc packsAll := by
    rw [h.1]; exact PackCode.of_bool packsAll_code
  have hP := packs_run (K := kernel) (A := asms) (L := L) (g := g) asms_pack v packsAll t hpc
    h.2.2.2.1 hsrc packsAll_dis (fun i _ => segFree (by rw [h.1]; omega))
  obtain ⟨h1pc, h1sub, h1acc, h1f⟩ := packRun_skel v packsAll t
  set t1 := packRun v t packsAll with ht1
  have hvo : ∀ j < 64, v (1763 + j) = d.o.getD j (b32 0) := fun j hj => valueOf_o d hj
  have hvp : ∀ q < 32, v (2346 + q) =
      joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)) :=
    fun q hq => valueOf_pack d hq
  have hpackv : ∀ q < 32, t1.regs (2346 + q) = some (v (2346 + q)) := by
    intro q hq
    rw [packRun_val v packsAll t packsAll_nodup (mem_packsAll q hq), hvp q hq,
      show 1763 + 2 * q = 1763 + (2 * q) from rfl,
      show 1764 + 2 * q = 1763 + (2 * q + 1) by omega, hvo _ (by omega), hvo _ (by omega)]
  have hc : t1.regs 2378 = some (v 2378) := by
    rw [packRun_val v packsAll t packsAll_nodup mem_packsAll_c]
    simp only [hv, valueOf_cpair, Prm.cpair]
    rfl
  have hcode : MulCodeC kernel 2378 t1.pc mulsAll := by
    rw [h1pc, h.1, packsAll_len]; exact MulCodeC.of_bool mulsAll_code
  have hM := mulsC_run (L := L) (g := g) v (c := 2378) (vc := v 2378) mulsAll t1 hcode
    (h1f.trans h.2.2.2.1) hc
    (fun m hm => by
      obtain ⟨q, hq, rfl⟩ := mulsAll_src m hm
      exact hpackv q hq)
    mulsAll_dis
    (fun i _ s hs => ⟨idealAt (Or.inl rfl) (by rw [hs, h1pc, h.1]; omega),
      declineAt (Or.inl rfl) (by rw [hs, h1pc, h.1]; omega)⟩)
  obtain ⟨h2pc, h2sub, h2acc, h2f⟩ := mulRunC_skel v (v 2378) mulsAll t1
  constructor
  · intro hok
    unfold D.loadOk at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hp, hm⟩ := hok
    have hr1 := hP.1 hp
    have hrun : run kernel asms L g 65 t = some (mulRunC v (v 2378) t1 mulsAll) := by
      have := run_comp hr1 (hM.1 hm)
      rwa [packsAll_len, mulsAll_len] at this
    refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h2pc, h1pc, h.1, packsAll_len, mulsAll_len]
    · rw [h2sub, h1sub, h.2.1]
    · rw [h2acc, h1acc, h.2.2.1]
    · rw [h2f, h1f, h.2.2.2.1]
    · refine Flow.holds_of_pointwise fun r hr => ?_
      rcases pm_cover r hr with hq | ⟨hl, hp1, hm1⟩
      · obtain ⟨q, hq', rfl⟩ : ∃ q, q < 32 ∧ r = 2479 + q := ⟨r - 2479, by omega, by omega⟩
        rw [mulRunC_val v (v 2378) mulsAll t1 mulsAll_nodup (mem_mulsAll q hq'), valueOf_prod d hq',
          D.prod, hsk, hvp q hq']
        simp [hv, valueOf_cpair]
      · rw [mulRunC_other v (v 2378) mulsAll t1 hm1, packRun_other v packsAll t hp1,
          reg_of hR hl]
  · intro hbad
    by_cases hp : packsOk v packsAll = true
    · have hm : mulsOkC v (v 2378) mulsAll = false := by
        have hbad' : (packsOk v packsAll && mulsOkC v (v 2378) mulsAll) = false := hbad
        rw [hp] at hbad'
        simpa using hbad'
      exact dead_of_run (hP.1 hp) (hM.2 hm)
    · exact hP.2 (by simpa using hp)

end
end PTX.Kernels.InklingRelDecode.Proof.Epi

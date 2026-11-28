-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QStore
import Tactics.KernelRfl

@[expose] public section

/-! # The strict run from one query store to the next -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The store `i` of the first seven, and the store after it. -/
abbrev f8 (i : Fin 7) : Fin 8 := ⟨i.val, by omega⟩
abbrev f8s (i : Fin 7) : Fin 8 := ⟨i.val + 1, by omega⟩

theorem sn_check : ∀ i : Fin 7,
    (∀ τ ∈ Data.tags (.stq (f8s i) 0), τ ∈ Data.tags (.stq (f8 i) 3) ∨ ∃ k : Fin 4, τ = .qw (f8s
        i) k) ∧
    (∀ (k : Fin 4) (b : Fin 2), Data.Tag.qh (Data.pk (f8s i) k b) ∈ Data.tags (.stq (f8 i) 3)) ∧
    (∀ k : Fin 4, 747 + 5 * (f8s i).val + k.val ∉ (Data.tags (.stq (f8 i) 3)).map Data.Tag.reg ∧
      747 + 5 * (f8s i).val + k.val ∉ ctlLive (528 + 6 * i.val)) ∧
    (ctlLive (532 + 6 * i.val)).isSublist (ctlLive (528 + 6 * i.val)) = true := by
  decide +kernel


theorem code_len : kernel.code.length = 2856 := by kernel_rfl

theorem sn_frame : ∀ i : Fin 7, frameB ((kernel.code.drop (527 + 6 * i.val)).take 1)
    (qKeys ++ (proQt (528 + 6 * i.val)).map Prod.fst) = true ∧
    tagsIn (proQt (528 + 6 * i.val)) (proQt (527 + 6 * i.val)) = true := by decide +kernel

/-- **From a store to the next**: the address, and the four packs of the next store. -/
theorem stq_next (c : Control.D) (v : Data.Vals) (hv : ∀ k, (v.q k).bytes = 2) (i : Fin 7) :
    SegQ kernel Assumptions.all L g (QT proQt) (527 + 6 * i.val)
      (dFacts Q L g w (dq c v (.stq (f8 i) 3))) (532 + 6 * i.val)
      (dFacts Q L g w (dq c v (.stq (f8s i) 0))) := by
  obtain ⟨ht, hq, hn, hl⟩ := sn_check i
  obtain ⟨hB, hT⟩ := sn_frame i
  let D := Data.dF Q L g (dq c v (.stq (f8 i) 3))
  have hnk : ∀ k : Fin 4, 747 + 5 * (f8s i).val + k.val ∉
      (D ++ facts Q L g w c (528 + 6 * i.val)).map Prod.fst := fun k h => by
    obtain ⟨p, hp, he⟩ := List.mem_map.mp h
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hp
      exact (hn k).1 (he ▸ List.mem_map_of_mem (f := Data.Tag.reg) hτ)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      exact (hn k).2 (he ▸ by simpa [facts, factsFrom_keys] using hr)
  have hl' : (ctlLive (Site.stq (f8s i) 0).pc).isSublist (ctlLive (528 + 6 * i.val)) = true := by
    have e : (Site.stq (f8s i) 0).pc = 532 + 6 * i.val := by
      have : (f8s i).val = i.val + 1 := rfl
      simp only [Site.pc]; omega
    rw [e]; exact hl
  have pk := packs4 (Q := Q) (L := L) (g := g) (dq c v (.stq (f8 i) 3)) (f8s i)
    (F := D ++ facts Q L g w c (528 + 6 * i.val)) (fun k b => List.mem_append_left _
      (List.mem_map_of_mem (f := fun τ => (τ.reg, τ.val Q L g (dq c v (.stq (f8 i) 3)))) (hq k b)))
    hv hnk
  rw [show 522 + 6 * (f8s i).val = 528 + 6 * i.val by have : (f8s i).val = i.val + 1 := rfl; omega,
    show 526 + 6 * (f8s i).val = 532 + 6 * i.val by have : (f8s i).val = i.val + 1 := rfl; omega]
        at pk
  refine SegQ.comp (b := 528 + 6 * i.val) (G := D ++ facts Q L g w c (528 + 6 * i.val))
    (SegQ.of_seg_pre (Dk := qKeys) (fun p hp => ?_) Lib.rulesFrame (seg_next_addr (Q := Q) (w := w)
      (d := c) i) (by omega) (by rw [code_len]; omega) (by omega)
      (PlainSegs.mono (plainSegs_pro (a := 27) (b := 574) le_rfl) (by omega) (by omega)) hB hT)
    (SegQ.comp pk (SegQ.sub fun q hq' => ?_))
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hp
    exact stq_keys _ _ τ hτ
  · rcases List.mem_append.mp hq' with h | h
    · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
      rw [tag_val_site (Q := Q) (L := L) (g := g) c v (.stq (f8s i) 0) (.stq (f8 i) 3) τ]
      rcases ht τ hτ with h1 | ⟨k, rfl⟩
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem
            (f := fun τ => (τ.reg, τ.val Q L g (dq c v (.stq (f8 i) 3)))) h1)))))
      · fin_cases k <;> simp [tf]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_append_right _ (mem_facts_sub hl' h)))))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict

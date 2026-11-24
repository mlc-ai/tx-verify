-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStage0a
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStage0b
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStage1a
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStage1b

@[expose] public section

/-! # Stage 1's first O-free arrival

The arrival continues through the setup (`CorrectionStepEntry`, `CorrectionStepEntryF`,
`CorrectionStepStage*`): the
first item's stage 0 barrier when the cluster has an item, else the tail's poll. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The same concrete state at a restated program counter. -/
theorem At.pc_eq {t : TState} {p q : Nat} {F : List (Nat × Value)} (h : At t p F) (e : p = q) :
    At t q F := e ▸ h

/-- From the branch past the item loop to the first item's stage 0 barrier. -/
theorem entry_loop (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g (8 + (8 + (1 + (2 + (1 + (2 + (1 + (8 + (7 + (4 + (3 + (4 + (3 + (1 +
      (2 + (5 + 1)))))))))))))))) 3785
      (factsX L g 3784 (dS aw a o)
        [(291, .pred (decide ¬ 0 < items L g)), (624, b32 (kOf L g))])
      (Site.sync 0 .first).pc (facts L g (dS aw a o)) := by
  have s1 := Seg.selp_imm_eq (K := kernel) (A := asms) (L := L) (g := g) (c := bit2 L g)
    (F := factsX L g 3801 (dS aw a o)
      [(295, .pred (bit2 L g)), (2721, b32 (trips L)), (2723, b32 0),
        (2725, b32 (2097152 * kOf L g))]) Flow.code_3801
    (mem_factsX (by table_decide) (by simp [valueX]))
    (not_mem_factsFrom (show 2727 ∉ Flow.live 3801 by table_decide))
    (selV_eq _ (a' := 64) (b' := 4294967232) (by decide) (by decide))
    (fun _ _ => asms_localRule_none) (segFree (by decide))
  have s2 := Seg.selp_imm_eq (K := kernel) (A := asms) (L := L) (g := g) (c := bit1 L g)
    (F := factsX L g 3804 (dS aw a o)
      [(296, .pred (bit1 L g)), (2721, b32 (trips L)), (2723, b32 0),
        (2725, b32 (2097152 * kOf L g)), (2727, b32 (selN (bit2 L g) 64 4294967232))])
      Flow.code_3804
    (mem_factsX (by table_decide) (by simp [valueX]))
    (not_mem_factsFrom (show 2729 ∉ Flow.live 3804 by table_decide))
    (selV_eq _ (a' := 32) (b' := 4294967264) (by decide) (by decide))
    (fun _ _ => asms_localRule_none) (segFree (by decide))
  have s3 := Seg.selp_imm_eq (K := kernel) (A := asms) (L := L) (g := g) (c := bit0 L g)
    (F := factsX L g 3807 (dS aw a o)
      [(297, .pred (bit0 L g)), (2721, b32 (trips L)), (2723, b32 0),
        (2725, b32 (2097152 * kOf L g)), (2727, b32 (selN (bit2 L g) 64 4294967232)),
        (2729, b32 (selN (bit1 L g) 32 4294967264))]) Flow.code_3807
    (mem_factsX (by table_decide) (by simp [valueX]))
    (not_mem_factsFrom (show 2731 ∉ Flow.live 3807 by table_decide))
    (selV_eq _ (a' := 4294967280) (b' := 16) (by decide) (by decide))
    (fun _ _ => asms_localRule_none) (segFree (by decide))
  exact Seg.comp (entry_b hpre aw a o) (Seg.comp (entry_c hpre aw a o) (Seg.comp s1
    (Seg.comp (entry_d hpre aw a o) (Seg.comp s2 (Seg.comp (entry_e hpre aw a o)
    (Seg.comp s3 (Seg.comp (entry_f1 hpre aw a o) (Seg.comp (entry_f2 hpre aw a o)
    (Seg.comp (entry_s0a hpre aw a o) (Seg.comp (entry_s0b hpre aw a o)
    (Seg.comp (entry_s1a hpre aw a o) (Seg.comp (entry_s1b hpre aw a o)
    (Seg.comp (entry_f5 hpre aw a o) (Seg.comp (entry_f6 hpre aw a o)
    (Seg.comp (entry_f7 hpre aw a o) (entry_f8 hpre aw a o))))))))))))))))

/-- No item: the branch reaches the tail's poll. -/
theorem entry_tail (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 0 Site.tailWait.pc
      (factsX L g 3784 (dS aw a o)
        [(291, .pred (decide ¬ 0 < items L g)), (624, b32 (kOf L g))])
      Site.tailWait.pc (facts L g ⟨.tailWait, 0, 0, aw, a, o⟩) := by
  intro t h
  corr_segx h hpre

/-- **Stage 1's first O-free arrival**, then the first item or the tail. -/
theorem step_free1 {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hs : d.site = .free 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl : i = 0 := hi.start (.inr (.inr ⟨1, rfl⟩))
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_15)
  obtain rfl := fires_next (show AdvancesOp (.mbarArrive _ _ _ _ _ _ _ none) from trivial) hf
  obtain ⟨t1, hr1, ht1⟩ := entry_a hpre hg tt aw a o _ (At.next h)
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
    (show kernel.code[Flow.bra_3784]? = _ from Flow.code_3784) (decide ¬ 0 < items L g) ht1
    (holds_mem ht1.2.2.2.2 (mem_factsX (by table_decide) (by simp [valueX])))
    asms_localRule_none
  by_cases hn : 0 < items L g
  · have ht2' := At.pc_eq ht2 (by simp [hn] : _ = 3785)
    obtain ⟨t3, hr3, ht3⟩ := entry_loop hpre aw a o _ ht2'
    exact step_of_run (d' := dS aw a o) (by simp [next, hn])
      ⟨fun _ => hn, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
        fun h' => by simp [Site.inTrip] at h', fun h' => by simp [Site.rescale] at h'⟩ rfl
      ⟨_, t3, run_comp hr1 (run_comp hr2 hr3), ht3⟩
  · have ht2' := At.pc_eq ht2 (by simp [hn]; rfl : _ = Site.tailWait.pc)
    obtain ⟨t3, hr3, ht3⟩ := entry_tail hpre aw a o _ ht2'
    exact step_of_run (d' := ⟨.tailWait, 0, 0, aw, a, o⟩) (by simp [next, hn])
      ⟨fun h' => by simp [Site.inItem] at h', fun _ _ _ _ => by simp only; omega,
        fun h' => by simp at h', fun h' => by simp [Site.inTrip] at h',
        fun h' => by simp [Site.rescale] at h'⟩ rfl
      ⟨_, t3, run_comp hr1 (run_comp hr2 hr3), ht3⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction

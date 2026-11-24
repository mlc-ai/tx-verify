-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxBase
public import Lemmas.Flow.BarReg

@[expose] public section

/-! # The softmax warps' item loop and exit

The register increase (then the start barrier), the stores of `α` and `l` to the statistics
word (then the named barrier), the named barrier after an item: the item register advances by
the number of clusters (`add.s32`, `setp.lt.s32`, `@p bra`, decided by `Work.loop_branch`) and
the thread enters the next item (the Tensor Memory addresses and the statistics barrier of the
stage are recomputed, `tmem_close`) or the tail's poll; the end barrier, then the exit (the role
test `w & -4 ≠ 8` sends the softmax warps to the `ret`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow Work

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}

/-- `setmaxnreg.inc 176`, then the start barrier. -/
theorem step_setMaxReg {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .setMaxReg)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_4)
  obtain rfl := fires_next (show AdvancesOp (.setMaxReg _ _) from trivial) hf
  have hst := hi.start (.inl rfl)
  refine step_of_run (d' := ⟨.bar0, i, tt, s, m, l⟩) (by simp [next])
    ⟨hi.warp, fun h => by simp [Site.inItem] at h, fun h => by simp at h,
      fun _ => hst, fun h => by simp [Site.tile0] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp at h, hi.lBytes⟩ rfl rfl ⟨0, ?_⟩
  sm_seg (At.next h) hpre

/-- The stores of `α` (then the loop trip's named barrier) and of `l` (then the item's last
named barrier). -/
theorem step_word {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .alphaSt ∨ d.site = .lSt)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  rcases hs with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_st rfl hf
    refine step_of_run (d' := ⟨.gen 1, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨0, ?_⟩
    rw [afterStore_one h.2.1]
    sm_seg (At.next h) hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_1)
    obtain ⟨a, bs, rfl, rfl⟩ := fires_st rfl hf
    have hit := hi.item rfl
    have hla := hi.last (.inl rfl)
    refine step_of_run (d' := ⟨.gen 2, i, tt, s, m, l⟩) (by simp [next])
      ⟨hi.warp, fun _ => hit, fun h => by simp at h, fun h => by simp at h,
        fun h => by simp [Site.tile0] at h, fun h => by simp [Site.inTrip] at h,
        fun _ => hla, hi.lBytes⟩ rfl rfl ⟨0, ?_⟩
    rw [afterStore_one h.2.1]
    sm_seg (At.next h) hpre

/-- The end barrier, then the role test and the exit. -/
theorem step_barEnd {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .barEnd) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_3)
  obtain ⟨rfl, rfl⟩ := fires_barArrive_imm (by decide) (by decide) (by decide) (by decide)
    (by rw [hpre.block]; decide) hf
  have ht := hi.tail (.inr (.inl rfl))
  refine step_of_run (d' := ⟨.exit, i, tt, s, m, l⟩) (by simp [next])
    ⟨hw8, fun h => by simp [Site.inItem] at h, fun _ => ht, fun h => by simp at h,
      fun h => by simp [Site.tile0] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp at h, hi.lBytes⟩ rfl rfl ?_
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 2 (PTX.next t) = some t1 ∧
      At t1 3752 (factsX L g 3752 ⟨.exit, i, tt, s, m, l⟩ [(290, .pred true)]) := by
    sm_seg (At.next h) hpre
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
    (show kernel.code[3752]? = _ from Flow.code_3752) true ht1
    (holds_mem ht1.2.2.2.2 (List.mem_map.mpr ⟨290, by table_decide, by simp [valueX]⟩))
    asms_localRule_none
  have hl : Flow.live Site.exit.pc = [] := rfl
  exact ⟨_, t2, run_comp hr1 hr2, ⟨by rw [ht2.1]; rfl, ht2.2.1, ht2.2.2.1, ht2.2.2.2.1,
    by simp [factsAt, hl, Flow.factsFrom]⟩⟩

/-- The loop test and the item register after an item (checkpoint facts). -/
def exItem (L : Launch) (g i : Nat) : List (Nat × Value) :=
  [(288, .pred (PTX.compare .lt .s 32 (rd (workW L g (i + 1))) (rd (totW L)))),
   (3930, .bits 32 (workW L g (i + 1)))]

/-- The checkpoint after an item in terms of the next state: the parities of the polls are
those of the next item's (or the tail's) first statistics poll. -/
theorem item_congr {L : Launch} {g i tt : Nat} {s : Nat → Value} {m l : Value} {site : Site}
    (hsite : site = .statsW 0 ∨ site = .statsW 3) (hla : tt + 1 = trips L) (r : Nat)
    (hr : r ∈ Flow.live 3740) :
    valueX L g ⟨.gen 2, i, tt, s, m, l⟩ (exItem L g i) r =
      valueX L g ⟨site, i + 1, 0, s, m, l⟩ [(288, .pred (PTX.compare .lt .s 32
        (rd (workW L g (i + 1))) (rd (totW L))))] r := by
  rw [show Flow.live 3740 = Flow.live_3740 from rfl] at hr
  simp only [Flow.live_3740, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hsite with rfl | rfl <;>
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [valueX, exItem, valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit,
    Option.getD_some, Option.getD_none, List.lookup_cons, List.lookup_nil, Nat.reduceBEq] <;>
  simp [statsIdx, tileIdx, Site.tile0, ← hla, Nat.mul_add, Nat.add_mul] <;> congr 1 <;> omega

/-- The last named barrier of an item, then the next item's first statistics poll or the
tail's. -/
theorem step_gen2 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .gen 2) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  have hit := hi.item rfl
  have hla := hi.last (.inr rfl)
  simp only at hit hla
  have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_2)
  have hr : t.regs 1017 = some (b32 (kOf L g + 3 + 4 * stOf L g)) :=
    (reg_of h (by table_decide)).trans rfl
  obtain ⟨-, rfl⟩ := fires_barArrive_reg hr (by simp only [stOf, kOf] at hk ⊢; omega)
    (by decide) (by decide) (by decide) (by rw [hpre.block]; decide) hf
  by_cases hT : i + 1 < items L g
  · let d' : D := ⟨.statsW 0, i + 1, 0, s, m, l⟩
    refine step_of_run (d' := d') (by simp [next, nextItem, hT, d'])
      ⟨hw8, fun _ => hT, fun h => by simp [d'] at h, fun h => by simp [d'] at h,
        fun _ => rfl, fun h => by simp [d', Site.inTrip] at h, fun h => by simp [d'] at h,
        hi.lBytes⟩ rfl rfl ?_
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 2 (PTX.next t) = some t1 ∧
        At t1 3740 (factsX L g 3740 ⟨.gen 2, i, tt, s, m, l⟩ (exItem L g i)) := by
      sm_seg (At.next h) hpre
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
      (show kernel.code[3740]? = _ from Flow.code_3740)
      (PTX.compare .lt .s 32 (rd (workW L g (i + 1))) (rd (totW L))) ht1
      (holds_mem ht1.2.2.2.2 (List.mem_map.mpr ⟨288, by table_decide, by simp [valueX, exItem]⟩))
      asms_localRule_none
    replace ht2 := at_congr ht2 (item_congr (site := d'.site) (by simp [d']) hla)
    rw [loop_branch hpre hit] at ht2
    simp only [hT, decide_true, ↓reduceIte] at ht2
    by_cases hw : 3 < warpOf L g
    · obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
          At t3 1245 (factsX L g 1245 d' [(146, .pred true)]) := by
        sm_seg ht2 hpre
      obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 14 t3 = some t4 ∧
          At t4 (Site.statsW 0).pc (factsAt L g (Site.statsW 0).pc d') := by
        sm_seg ht3 hpre
      exact ⟨_, t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, ht4⟩
    · obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
          At t3 1245 (factsX L g 1245 d' [(146, .pred false)]) := by
        sm_seg ht2 hpre
      obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 14 t3 = some t4 ∧
          At t4 (Site.statsW 0).pc (factsAt L g (Site.statsW 0).pc d') := by
        sm_seg ht3 hpre
      exact ⟨_, t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, ht4⟩
  · let d' : D := ⟨.statsW 3, i + 1, 0, s, m, l⟩
    refine step_of_run (d' := d') (by simp [next, nextItem, hT, d'])
      ⟨hw8, fun h => by simp [d', Site.inItem] at h, fun _ => ⟨by simp [d']; omega, rfl⟩,
        fun h => by simp [d'] at h, fun h => by simp [d', Site.tile0] at h,
        fun h => by simp [d', Site.inTrip] at h, fun h => by simp [d'] at h,
        hi.lBytes⟩ rfl rfl ?_
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 2 (PTX.next t) = some t1 ∧
        At t1 3740 (factsX L g 3740 ⟨.gen 2, i, tt, s, m, l⟩ (exItem L g i)) := by
      sm_seg (At.next h) hpre
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
      (show kernel.code[3740]? = _ from Flow.code_3740)
      (PTX.compare .lt .s 32 (rd (workW L g (i + 1))) (rd (totW L))) ht1
      (holds_mem ht1.2.2.2.2 (List.mem_map.mpr ⟨288, by table_decide, by simp [valueX, exItem]⟩))
      asms_localRule_none
    replace ht2 := at_congr ht2 (item_congr (site := d'.site) (by simp [d']) hla)
    rw [loop_branch hpre hit] at ht2
    simp only [hT, decide_false, Bool.false_eq_true, ↓reduceIte] at ht2
    by_cases hw : 3 < warpOf L g
    · obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
          At t3 3742 (factsX L g 3742 d' [(289, .pred true)]) := by
        sm_seg ht2 hpre
      obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 4 t3 = some t4 ∧
          At t4 (Site.statsW 3).pc (factsAt L g (Site.statsW 3).pc d') := by
        sm_seg ht3 hpre
      exact ⟨_, t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, ht4⟩
    · obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
          At t3 3742 (factsX L g 3742 d' [(289, .pred false)]) := by
        sm_seg ht2 hpre
      obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 4 t3 = some t4 ∧
          At t4 (Site.statsW 3).pc (factsAt L g (Site.statsW 3).pc d') := by
        sm_seg ht3 hpre
      exact ⟨_, t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, ht4⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax

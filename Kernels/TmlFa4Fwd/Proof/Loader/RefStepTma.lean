-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.RefBase
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's reference invariant across warp 14's TMA groups and the drain

A TMA group's or the drain's event is neither a commit nor a local store, so the count fields
stay (`counts_other`); the step spec records the event's class (a successful poll, a won election,
an expect-tx arrival, a tensor copy). The fourth group's last election clears the first Bias
parity, the sixth flips both Bias parities; the seventh ends in the steady rounds or the second
pass. The drain's polls are on the slots of the next three packets. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi add32 shl)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (sbW)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

theorem tw_loc (hp : Pre p L m) (t : Fin 7) {v : V} {kk : Fin 2} :
    smLoc L g (rv p L g w ⟨.tw t, v, kk⟩ (waitRegs (.tw t)).1) 0 = bl L g (twOff t) := by
  fin_cases t <;> exact (smLoc_addi hp _ (by norm_num)).trans rfl

theorem ta_loc (hp : Pre p L m) (t : Fin 7) {v : V} {kk : Fin 2} :
    smLoc L g (rv p L g w ⟨.ta t, v, kk⟩ (taRegs (.ta t)).1) (taRegs (.ta t)).2.1 =
      bl L g (taOff t) := by
  fin_cases t
  · exact (smLoc_sb hp 0 (by norm_num)).trans rfl
  · exact (smLoc_addi hp 320 (by norm_num)).trans rfl
  · exact (smLoc_sb hp 8 (by norm_num)).trans rfl
  · exact (smLoc_sb hp 328 (by norm_num)).trans rfl
  · exact (smLoc_addi hp 320 (by norm_num)).trans rfl
  · exact (smLoc_sb hp 328 (by norm_num)).trans rfl
  · exact (smLoc_addi hp 320 (by norm_num)).trans rfl

theorem flip_bq {x : BitVec 64} {r : Nat} (h : x = BitVec.ofNat 64 (r % 2)) :
    groupEnd.xori x 1 = BitVec.ofNat 64 ((r + 1) % 2) := by
  have : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases this with h2 | h2
  · rw [h, h2, show (r + 1) % 2 = 1 by omega]; decide
  · rw [h, h2, show (r + 1) % 2 = 0 by omega]; decide

set_option hygiene false in
/-- Close the ring conjuncts of a group's successor. -/
macro "tma_ring" : tactic => `(tactic| (
  try simp only [refRing_iff, RingWords, SlotIs, ringCls,
    Site.isTma, Epilogue.Scan.late, Fin.isValue,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, imp_false, not_false_eq_true,
    true_and, and_true, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceLT, decide_true,
    decide_false, reduceCtorEq, false_implies, forall_const, Nat.le_add_left, le_refl,
    Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, true_implies, and_self,
    Nat.reduceEqDiff, Fin.reduceFinMk, Fin.mk_one, Nat.lt_irrefl] at hJ ⊢
  all_goals first
    | exact hJ
    | exact hJ.1
    | trivial
    | decide
    | exact ⟨hJ.1, hJ.2⟩
    | (obtain ⟨h2, h3, h4⟩ := hJ
       exact ⟨h2, by rw [h3], flip_bq (by simpa using h4)⟩)
    | (obtain ⟨rfl, h2⟩ := hJ; exact ⟨rfl, by decide⟩)
    | (obtain ⟨rfl, h2⟩ := hJ; exact h2)
    | (obtain ⟨rfl, h2⟩ := hJ; exact h2.1)
    | (obtain ⟨rfl, h2, h3, h4⟩ := hJ
       exact ⟨h2, by rw [h3], flip_bq (by simpa using h4)⟩)
    | (obtain ⟨rfl, h2, h3, h4⟩ := hJ
       exact ⟨rfl, h2, by rw [h3], flip_bq (by simpa using h4)⟩)
    | exact ⟨hJ.1, by decide⟩
    | (obtain ⟨_, -⟩ := hJ; decide)
    | (obtain ⟨rfl, -⟩ := hJ; (try simp only [↓reduceIte]); all_goals decide)
    | (obtain ⟨rfl, h2⟩ := hJ; exact by simpa using h2)))

/-- An event at a TMA group or the drain is neither a commit nor a local store. -/
theorem cls_cs {e : Event} {X : Option Cnt} (h : ∀ c, cls L g c e = decide (X = some c))
    (hX : ∀ c, X = some c → c ≠ .commit ∧ ∀ o, c ≠ .lst o) :
    cls L g .commit e = false ∧ ∀ o, cls L g (.lst o) e = false := by
  refine ⟨?_, fun o => ?_⟩ <;> rw [h] <;> simp only [decide_eq_false_iff_not] <;> intro hc
  · exact (hX _ hc).1 rfl
  · exact (hX _ hc).2 o rfl

set_option hygiene false in
/-- Close a branch of a TMA group's or the drain's step. -/
macro "tma_close" : tactic => `(tactic| (
  have hcs := cls_cs hcls (by
    intro c hc; cases hc
    all_goals exact ⟨by simp, by simp⟩)
  first
    | exact ⟨⟨k, A, by tma_ring, counts_other hC hcs.1 hcs.2 rfl⟩, by move_tac⟩
    | exact ⟨⟨k, k, by tma_ring, counts_other hC hcs.1 hcs.2 rfl⟩, by move_tac⟩))

set_option maxHeartbeats 8000000 in
theorem step_tw (hp : Pre p L m) (t : Fin 7) : StepRef p L g w (.tw t) := by
  intro v kk n e d' k A hJ hC hev hub hn
  have hw14 : w = 14 := hJ.1 rfl
  subst hw14
  simp only [Ev] at hev
  obtain ⟨ok, hk⟩ := hev
  rw [tw_loc hp t] at hk
  simp only [succ, hk] at hn
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hcls := cls_none (cls_waitF (L := L) (g := g) hk)
    exact ⟨⟨k, A, hJ, counts_quiet hC (cls_waitF hk) rfl⟩, by move_tac⟩
  · simp only [↓reduceIte, Option.some.injEq, D.mk'] at hn
    subst hn
    have hcls := cls_wait (L := L) (g := g) hk
    exact ⟨⟨k, A, refRing_congr hJ rfl rfl rfl rfl rfl rfl rfl,
      counts_other hC (by simp [cls, hk]) (fun _ => by simp [cls, hk]) rfl⟩, by move_tac⟩

set_option maxHeartbeats 8000000 in
theorem step_te (t : Fin 7) (i : Fin 3) : StepRef p L g w (.te t i) := by
  intro v kk n e d' k A hJ hC hev hub hn
  have hw14 : w = 14 := hJ.1 rfl
  subst hw14
  simp only [Ev] at hev
  rcases hev with ⟨inst, ld, hpc, hk⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  simp only [succ, hk] at hn
  by_cases hl : laneOf L g = ld
  · simp only [hl, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hcls := cls_won (L := L) (g := g) hk hl
    rw [hpc] at hcls
    fin_cases t <;> fin_cases i <;>
      simp only [teElected, D.mk', Fin.isValue, Fin.reduceFinMk, Fin.val_zero, Fin.val_one,
        Fin.val_two, ↓reduceIte, Nat.reduceEqDiff] <;>
      tma_close
  · simp only [hl, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hcls := cls_none (cls_lost (L := L) (g := g) hk hl)
    fin_cases t <;> fin_cases i
    all_goals get_k2
    all_goals
      simp only [teNext, groupEnd, afterTail, pgEnter, passStart, D.mk', D.ite, D.iteS,
        Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte, Nat.reduceEqDiff]
    all_goals try split_ifs
    all_goals tma_close

set_option maxHeartbeats 8000000 in
theorem step_ta (hp : Pre p L m) (t : Fin 7) : StepRef p L g w (.ta t) := by
  intro v kk n e d' k A hJ hC hev hub hn
  have hw14 : w = 14 := hJ.1 rfl
  subst hw14
  simp only [Ev] at hev
  rw [ta_loc hp t] at hev
  simp only [succ, Option.some.injEq, D.mk'] at hn
  subst hn
  have hcls := cls_arr (L := L) (g := g) hev
  exact ⟨⟨k, A, refRing_congr hJ rfl rfl rfl rfl rfl rfl rfl,
    counts_other hC (by simp [cls, hev]) (fun _ => by simp [cls, hev]) rfl⟩, by move_tac⟩

set_option maxHeartbeats 8000000 in
theorem step_tc (t : Fin 7) (c : Fin 2) : StepRef p L g w (.tc t c) := by
  intro v kk n e d' k A hJ hC hev hub hn
  have hw14 : w = 14 := hJ.1 rfl
  subst hw14
  simp only [Ev] at hev
  rcases hev with ⟨a, s, hk, -⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  have hcls := cls_copy (L := L) (g := g) (e := e) (.inr ⟨_, _, hk⟩)
  fin_cases t <;> fin_cases c
  all_goals get_k2
  all_goals
    simp only [succ, groupEnd, afterTail, pgEnter, passStart, D.mk', D.ite, D.iteS, Fin.isValue,
      Fin.val_zero, Fin.val_one, Option.some.injEq, ↓reduceIte, Nat.reduceEqDiff] at hn
  all_goals try split_ifs at hn
  all_goals subst hn
  all_goals tma_close

/-! ### The drain -/

/-- The empty barrier of the drain's poll `j`: the slot of packet `A + j`. -/
theorem dw_loc (hp : Pre p L m) (j : Fin 3) {v : V} {kk : Fin 2} {k A : Nat}
    (hJ : RefRing p L g w ⟨.dw j, v, kk⟩ k A) :
    smLoc L g (rv p L g w ⟨.dw j, v, kk⟩ (waitRegs (.dw j)).1) 0 =
      bl L g (56 + 8 * ((A + j.val) % 3)) := by
  have hS : SlotIs v A := hJ.2
  fin_cases j
  · exact (congrArg (smLoc L g · 0) (by
      show addi (add32 (sbW L) (shl v.slot 3)) 56 = _
      rw [hS.1])).trans (smLoc_empty hp A)
  · exact (congrArg (smLoc L g · 0) (by
      show addi (add32 (sbW L) (shl (nslot v.slot) 3)) 56 = _
      rw [(slotIs_next hS).1])).trans (smLoc_empty hp (A + 1))
  · exact (congrArg (smLoc L g · 0) (by
      show addi (add32 (sbW L) (shl (nslot (nslot v.slot)) 3)) 56 = _
      rw [show nslot (nslot v.slot) = _ from (slotIs_roundV hS).1])).trans (smLoc_empty hp (A + 2))

set_option maxHeartbeats 8000000 in
theorem step_dw (hp : Pre p L m) (hw : w = 14 ∨ w = 15) (j : Fin 3) :
    StepRef p L g w (.dw j) := by
  intro v kk n e d' k A hJ hC hev hub hn
  simp only [Ev] at hev
  obtain ⟨ok, hk⟩ := hev
  rw [dw_loc hp j hJ] at hk
  simp only [succ, hk] at hn
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hcls := cls_none (cls_waitF (L := L) (g := g) hk)
    exact ⟨⟨k, A, hJ, counts_quiet hC (cls_waitF hk) rfl⟩, by move_tac⟩
  · simp only [↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hcls := cls_wait (L := L) (g := g) hk
    have hc0 : n .commit = A := by simpa [arrAt, inPkt] using hC.commit
    have hcs : cls L g .commit e = false ∧ ∀ o, cls L g (.lst o) e = false :=
      ⟨by simp [cls, hk], fun _ => by simp [cls, hk]⟩
    fin_cases j <;> simp only [dwNext, D.mk', D.ite, Fin.isValue]
    all_goals try split_ifs
    all_goals refine ⟨⟨k, A, ⟨fun h => ?_, hJ.2⟩, counts_other hC hcs.1 hcs.2 rfl⟩,
      by move_with (by
        simp only [tag, Tag.cnt, hc0, reduceCtorEq, ↓reduceIte, Fin.isValue]; try rfl)⟩
    all_goals first
      | (simp [Site.isTma] at h; done)
      | exact w14_of hw (by simpa using ‹¬not14 w = true›)

set_option maxHeartbeats 8000000 in
theorem step_dq (hp : Pre p L m) : StepRef p L g w .dq := by
  intro v kk n e d' k A hJ hC hev hub hn
  have hw14 : w = 14 := hJ.1 rfl
  subst hw14
  simp only [Ev] at hev
  obtain ⟨ok, hk⟩ := hev
  rw [show smLoc L g (rv p L g 14 ⟨.dq, v, kk⟩ (waitRegs .dq).1) 0 = bl L g 24 from
    (smLoc_addi hp 24 (by norm_num)).trans rfl] at hk
  simp only [succ, hk] at hn
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hcls := cls_none (cls_waitF (L := L) (g := g) hk)
    exact ⟨⟨k, A, hJ, counts_quiet hC (cls_waitF hk) rfl⟩, by move_tac⟩
  · simp only [↓reduceIte, Option.some.injEq, D.mk'] at hn
    subst hn
    have hcls := cls_wait (L := L) (g := g) hk
    exact ⟨⟨k, A, ⟨fun _ => rfl, hJ.2⟩,
      counts_other hC (by simp [cls, hk]) (fun _ => by simp [cls, hk]) rfl⟩, by move_tac⟩

set_option maxHeartbeats 8000000 in
theorem step_de : StepRef p L g w .de := by
  intro v kk n e d' k A hJ hC hev hub hn
  have hw14 : w = 14 := hJ.1 rfl
  subst hw14
  simp only [Ev] at hev
  rcases hev with ⟨inst, ld, hpc, hk⟩ | ⟨f, hk⟩
  swap; exact absurd hk (hub f)
  simp only [succ, hk] at hn
  by_cases hl : laneOf L g = ld
  · simp only [hl, ↓reduceIte, Option.some.injEq, D.mk'] at hn
    subst hn
    have hcls := cls_won (L := L) (g := g) hk hl
    rw [hpc] at hcls
    exact ⟨⟨k, A, ⟨fun _ => rfl, hJ.2⟩,
      counts_other hC (by simp [cls, hk]) (fun _ => by simp [cls, hk]) rfl⟩, by move_tac⟩
  · simp only [hl, ↓reduceIte, Option.some.injEq, D.mk'] at hn
    subst hn
    have hcls := cls_none (cls_lost (L := L) (g := g) hk hl)
    exact ⟨⟨k, A, ⟨fun h => by simp [Site.isTma] at h, hJ.2⟩,
      counts_quiet hC (cls_lost hk hl) rfl⟩, by move_tac⟩

set_option maxHeartbeats 8000000 in
theorem step_da (hp : Pre p L m) : StepRef p L g w .da := by
  intro v kk n e d' k A hJ hC hev hub hn
  have hw14 : w = 14 := hJ.1 rfl
  subst hw14
  simp only [Ev] at hev
  rw [show smLoc L g (rv p L g 14 ⟨.da, v, kk⟩ (taRegs .da).1) (taRegs .da).2.1 = bl L g 8 from
    (smLoc_sb hp 8 (by norm_num)).trans rfl] at hev
  simp only [succ, Option.some.injEq, D.mk'] at hn
  subst hn
  have hcls := cls_arr (L := L) (g := g) hev
  exact ⟨⟨k, A, ⟨fun h => by simp [Site.isTma] at h, hJ.2⟩,
    counts_other hC (by simp [cls, hev]) (fun _ => by simp [cls, hev]) rfl⟩, by move_tac⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader

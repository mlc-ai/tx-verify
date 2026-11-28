-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefArith

@[expose] public section

/-! # Warpgroup 0's reference invariant is kept by every step

The six mbarrier sites (`next_arrL`, `next_wv`, `next_wq`, `next_arrV`, `next_arrS`, `next_wsv`),
the plain sites (`next_plain`), joined in `core_step`; `ref_step`: from a state with `Ref`, an
event of the state's shape that the machine follows leads to a state with `Ref` for the bumped
counts (an undefined-behaviour event bumps the class `ub`, after which `Ref` asks nothing). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem last_eq : (objs L g).last = smLoc L g (arrW L) 0 := by unfold objs lastL; rfl
theorem vReady_eq (j : Nat) : (objs L g).vReady j = smLoc L g (slotW L (W j) 222840) 0 := by
  unfold objs vReadyL; rfl
theorem vFree_eq (j : Nat) : (objs L g).vFree j = smLoc L g (slotW L (W j) 222872) 0 := by
  unfold objs vFreeL; rfl
theorem qk_eq (j : Nat) : (objs L g).qk j = smLoc L g (slotW L (W j) 222904) 0 := by
  unfold objs qkL; rfl
theorem so_eq (j : Nat) : (objs L g).so j = smLoc L g (slotW L (W j) 222920) 0 := by
  unfold objs soL; rfl
theorem sv_eq (j : Nat) : (objs L g).sv j = smLoc L g (slotW L (W j) 222936) 0 := by
  unfold objs svL; rfl

/-- The arrivals do not change before place 3, the polls not after place 2. -/
theorem arr_lo {O : Objs} {a : Bool} {r i i' : Nat} (h : i < 3) (h' : i' < 3) (l : Loc) :
    arrCnt O a r i l = arrCnt O a r i' l := by
  simp only [arrCnt, use, ind, show ¬ 3 ≤ i by omega, show ¬ 3 ≤ i' by omega, and_false,
    ↓reduceIte]

theorem acq_hi {O : Objs} {r : Nat} (l : Loc) : acqCnt O r 3 none l = acqCnt O r 2 none l := by
  simp only [acqCnt, use, ind, show 1 ≤ 3 by omega, show 1 ≤ 2 by omega, show 2 ≤ 3 by omega,
    show 2 ≤ 2 by omega, and_true]

/-- A poll that fails keeps the state: a plain step. -/
theorem poll_fail {d : D} {n : Cnt → Nat} {e : Event} {m : Loc} {q : Nat} {a : Bool}
    {sc : MbarScope} (hk : e.kind = .wait m q false a sc) (hJ : RefCore L g d n) :
    RefCore L g d (Code.bump cls n e) :=
  step_same (by simp [isMb, hk]) hJ (.inl ⟨rfl, rfl, rfl⟩)

set_option hygiene false in
/-- Open a poll site's step: the poll's success `hk`, or its failure (closed). -/
macro "w0_poll_step" : tactic => `(tactic| (
  intro d n e d' hd hpc hu hJ hev hn
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hd
  subst hd
  simp only [EvK, PollEv] at hev
  obtain ⟨ok, hk⟩ := hev.resolve_right (fun ⟨f, hf⟩ => hu f hf)
  simp only [succ, poll, hk] at hn
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
    subst hn
    exact poll_fail hk hJ
  simp only [↓reduceIte, Option.some.injEq] at hn
  subst hn
  have hb := bump_acq (n := n) hpc hk
  unfold RefCore at hJ ⊢
  simp only [Site.reg, Site.idx, Control.D.words, RefAt] at hJ ⊢))

theorem next_wv : StepRef P L g w .wv := by
  w0_poll_step
  obtain ⟨r, hl, ha, hr⟩ := hJ
  have ⟨_, _, _, _, _, hvs, _⟩ := hl
  dsimp only at hvs
  refine ⟨r, hl, fun l => ?_, fun l => ?_⟩
  · rw [(hb l).1, ha l, acq_wv, vReady_eq]
    simp only [vReadyW, r19W, slotW, hvs]
  · rw [(hb l).2, hr l]
    exact arr_lo (by omega) (by omega) l

theorem next_wq : StepRef P L g w .wq := by
  w0_poll_step
  obtain ⟨r, hl, ha, hr⟩ := hJ
  have ⟨_, _, _, _, _, _, _, hsl, _⟩ := hl
  dsimp only at hsl
  refine ⟨r, hl, fun l => ?_, fun l => ?_⟩
  · rw [(hb l).1, ha l, acq_wq, qk_eq]
    simp only [qkW, r20W, slotW, hsl]
  · rw [(hb l).2, hr l]
    exact arr_lo (by omega) (by omega) l

theorem next_wsv : StepRef P L g w .wsv := by
  w0_poll_step
  obtain ⟨he, ha, hr⟩ := hJ
  have ⟨hsl, _⟩ := he
  dsimp only at hsl
  refine ⟨he, fun l => ?_, fun l => ?_⟩
  · rw [(hb l).1, ha l]
    simp only [Nat.reduceEqDiff, ↓reduceIte, acq_sv, sv_eq, svW, r20W, slotW, hsl, svSlot]
  · rw [(hb l).2, hr l]

theorem some_some_eq {X Y : D} (h : some (some X) = some (some Y)) : Y = X :=
  (Option.some.inj (Option.some.inj h)).symm

set_option hygiene false in
/-- Open an arrival site's step: the arrival `hk`, the bumped counts `hb`. -/
macro "w0_arr_step" : tactic => `(tactic| (
  intro d n e d' hd hpc hu hJ hev hn
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hd
  subst hd
  simp only [EvK, ArrEv] at hev
  have hk := hev.resolve_right (fun ⟨f, hf⟩ => hu f hf)
  have hb := bump_arrive (n := n) hpc hk
  unfold RefCore at hJ ⊢
  simp only [succ] at hn))

theorem next_arrV : StepRef P L g w .arrV := by
  w0_arr_step
  obtain rfl := some_some_eq hn
  simp only [Site.reg, Site.idx, Control.D.words, RefAt] at hJ ⊢
  obtain ⟨r, hl, ha, hr⟩ := hJ
  have ⟨_, _, _, _, _, hvs, _⟩ := hl
  dsimp only at hvs
  refine ⟨r, hl, fun l => ?_, fun l => ?_⟩
  · rw [(hb l).1, ha l]
    exact (acq_hi l).symm
  · rw [(hb l).2, hr l, arr_arrV, vFree_eq]
    simp only [vFreeW, r19W, slotW, hvs]

theorem next_arrL : StepRef P L g w .arrL := by
  w0_arr_step
  obtain rfl := some_some_eq hn
  simp only [Site.reg, RefAt] at hJ
  obtain ⟨ha, hr⟩ := hJ
  have hlast : ∀ l, Code.bump cls n e (.arrive l) = arrCnt (objs L g) true 0 0 l := fun l => by
    rw [(hb l).2, hr l, arr_last, last_eq]
  cases h : scmpi .lt .s (r15 l0 l1) 64
  · obtain ⟨h1, h26, hnb⟩ := rounds_range h
    simp only [loopEntry, h, Bool.false_eq_true, ↓reduceIte, Site.reg, Site.idx,
      Control.D.words, RefAt]
    refine ⟨0, ⟨h, h26, h1, show i32 1 = W (0 + 1) by decide, ?_,
      show i32 0 = W (0 % 4) by decide, show i16 0 = W (0 / 4 % 2) by decide,
      show i32 0 = W (0 % 2) by decide, show i16 0 = W (0 / 2 % 2) by decide⟩, fun l => ?_, hlast⟩
    · dsimp only
      rw [hnb, cnt_init h1 h26]
    · rw [(hb l).1, ha l]
  · have h0 : rounds l0 l1 = 0 := by simp [rounds, h]
    simp only [loopEntry, h, ↓reduceIte, Site.reg, Site.idx, Control.D.words, RefAt, EpiOk,
      h0]
    refine ⟨⟨show i32 0 = W ((0 - 1) % 2) by decide, show i16 0 = W ((0 - 1) / 2 % 2) by decide⟩,
      fun l => ?_, hlast⟩
    rw [(hb l).1, ha l]
    rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

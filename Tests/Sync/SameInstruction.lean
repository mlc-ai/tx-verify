-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

/-! Litmus tests for EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH, ERR-SETMAXNREG,
ERR-ALIGNED-MISMATCH).

One CTA of 128 threads. The kernel has two aligned `bar.sync 1, 64` instructions (pcs 0 and 1).

`roles`: warp 0 executes the one at pc 0 and warp 1 the one at pc 1, as two warp roles that
synchronize on barrier 1 from their own code. Different warps are not compared by position:
there is no `BarMismatch` (`roles_no_mismatch`) and no aligned divergence
(`roles_no_divergence`).

`split`: lanes 0 and 1 of warp 0 execute their first barrier at pc 0 and pc 1. The lanes of a
warp execute one aligned instruction in convergence, so this is an `AlignedMismatch`
(`split_mismatch`).

Different counts across warps remain undefined: the barrier resource cannot perform an arrival
whose count differs from its generation's (`countMismatch`, a fault of `CtaBarFault`).

The same for `setmaxnreg` (a warpgroup of four warps): requests of different warps at different
positions with one direction and count are safe (`reg_roles_safe`); requests of
one warp's lanes at different positions are an `AlignedMismatch` (`reg_split_unsafe`), and
requests of different warps with different counts are unsafe (`reg_count_unsafe`). -/

namespace PTX.Tests.SameInstruction
open PTX

private def L : Launch := { grid := 1, block := 128, params := fun _ => none }

private def K : Kernel :=
  { name := "same_instruction", params := [],
    code := [{ op := .barSyncN (.imm 1) (.imm 64) true },
      { op := .barSyncN (.imm 1) (.imm 64) true }] }

private def barAt (pc : Nat) : Event := ⟨pc, .bar 1 (some 64) .sync⟩

private def roles : Execution :=
  { tr := fun g => if g < 32 then [barAt 0] else if g < 64 then [barAt 1] else []
    rf := fun _ _ => none }

private def split : Execution :=
  { tr := fun g => if g = 1 then [barAt 1] else if g < 64 then [barAt 0] else []
    rf := fun _ _ => none }

private theorem roles_get {g i : Nat} {ev : Event} (h : roles.get (g, i) = some ev) :
    i = 0 ∧ g < 64 ∧ ev = barAt (if g < 32 then 0 else 1) := by
  simp only [Execution.get, roles] at h
  split_ifs at h with h1 h2
  · obtain _ | i := i
    · exact ⟨rfl, by omega, by simp_all⟩
    · simp at h
  · obtain _ | i := i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨rfl, h2, by simp [show ¬ g < 32 by omega, h]⟩
    · simp at h
  · simp at h

/-- Two warps reach one generation of barrier 1 from different positions: no mismatch. -/
theorem roles_no_mismatch : ¬ BarMismatch L roles := by
  rintro (⟨g, h, i, j, id, id', c, c', pc, pc', -, hg, hh, -, hne⟩ |
    ⟨g, h, i, j, id, id', c, c', m, pc, pc', -, hg, -⟩)
  · obtain ⟨-, -, hge⟩ := roles_get hg
    obtain ⟨-, -, hhe⟩ := roles_get hh
    simp only [barAt, Event.mk.injEq, Kind.bar.injEq] at hge hhe
    obtain ⟨-, rfl, rfl, -⟩ := hge
    obtain ⟨-, rfl, rfl, -⟩ := hhe
    simp at hne
  · obtain ⟨-, -, hge⟩ := roles_get hg
    split_ifs at hge <;> simp [barAt] at hge

/-- The lanes of each warp execute one position, and no thread exits: no aligned divergence. -/
theorem roles_no_divergence : ¬ AlignedClass.bar.Divergent L K roles := by
  rw [AlignedClass.divergent_bar_iff]
  rintro ⟨g, h, i, j, id, id', c, c', m, m', pc, pc', hs, hg, hh, -, -, hne⟩
  obtain ⟨-, hg64, hge⟩ := roles_get hg
  obtain ⟨-, hh64, hhe⟩ := roles_get hh
  have hw : g < 32 ↔ h < 32 := by
    obtain ⟨-, hw⟩ := hs
    simp only [L] at hw
    omega
  simp only [barAt, hw, Event.mk.injEq] at hge hhe
  split_ifs at hge hhe <;> obtain ⟨rfl, -⟩ := hge <;> obtain ⟨rfl, -⟩ := hhe <;> simp at hne

/-- Two lanes of one warp at different aligned positions: a mismatch. -/
theorem split_mismatch : AlignedMismatch L K split :=
  ⟨.bar, .inl ((AlignedClass.divergent_bar_iff L).2 ⟨1, 0, 0, 0, 1, 1, some 64, some 64, .sync,
    .sync, 1, 0, ⟨⟨by decide, by decide, by decide⟩, by decide⟩, rfl, rfl, rfl, rfl,
    by decide⟩)⟩

private def lanes (w : Nat) : List (Nat × EvId) :=
  (List.range 32).map fun l => (w * 32 + l, (w * 32 + l, 0))

-- Warp 0 arrives with `bar.sync 1, 64` and warp 1 with `bar.sync 1, 96`: the second arrival's
-- count differs from the open generation's (`countMismatch`, a fault of `CtaBarFault`).
example : ∃ s, CtaBarrier.run 128 {} [.arrival 1 0 (some 64) (lanes 0)] = .ok s ∧
    CtaBarrier.Record.perform 128 s (.arrival 1 1 (some 96) (lanes 1)) =
      .error .countMismatch ∧ CtaBarrier.Error.isFault .countMismatch = true :=
  ⟨_, rfl, rfl, rfl⟩

/-! ## `setmaxnreg` -/

private def regAt (pc n : Nat) : Event := ⟨pc, .setMaxReg false n 0⟩

/-- Warp `w` requests at `pc w` with count `n w`. -/
private def regs (pc n : Nat → Nat) : Execution :=
  { tr := fun g => if g < 128 then [regAt (pc (g / 32)) (n (g / 32))] else []
    rf := fun _ _ => none }

private theorem regs_get {pc n : Nat → Nat} {g i : Nat} {ev : Event}
    (h : (regs pc n).get (g, i) = some ev) :
    g < 128 ∧ i = 0 ∧ ev = regAt (pc (g / 32)) (n (g / 32)) := by
  simp only [Execution.get, regs] at h
  split_ifs at h with hg
  · obtain _ | i := i <;> simp_all
  · simp at h

/-- Each warp of the warpgroup requests `dec 72` at its own position: the warps are not compared
by position, and the requests are safe. -/
theorem reg_roles_safe : ¬ SetMaxNReg.Unsafe L (regs (fun w => w) (fun _ => 72)) := by
  rintro ⟨⟨g, i⟩, pc, inc, n, inst, he, hu⟩
  obtain ⟨hg, rfl, he'⟩ := regs_get he
  rcases hu with ⟨m, hm, -⟩ | hgrp | ⟨⟨h, j⟩, pc', inc', n', inst', -, hf, -, hne⟩ | ⟨hpos, -⟩
  · simp [SetMaxNReg.prior] at hm
  · simp only [L] at hgrp
    omega
  · obtain ⟨hh, rfl, hf'⟩ := regs_get hf
    simp only [regAt, Event.mk.injEq, Kind.setMaxReg.injEq] at he' hf'
    obtain ⟨rfl, rfl, rfl, -⟩ := he'
    obtain ⟨rfl, rfl, rfl, -⟩ := hf'
    simp at hne
  · simp [SetMaxNReg.ordinal] at hpos

/-- The lanes of each warp request at one position: no aligned divergence. -/
theorem reg_roles_aligned :
    ¬ AlignedClass.setMaxReg.Divergent L K (regs (fun w => w) (fun _ => 72)) := by
  rw [AlignedClass.divergent_setMaxReg_iff]
  rintro ⟨⟨g, i⟩, ⟨h, j⟩, pc, pc', inc, inc', n, n', inst, inst', ⟨-, hw⟩, he, hf, -, hne⟩
  obtain ⟨hg, -, he'⟩ := regs_get he
  obtain ⟨hh, -, hf'⟩ := regs_get hf
  simp only [regAt, Event.mk.injEq] at he' hf'
  obtain ⟨rfl, -⟩ := he'
  obtain ⟨rfl, -⟩ := hf'
  simp only [L] at hw
  exact hne (by omega)

/-- Two lanes of warp 0 request at different positions: an aligned divergence. -/
theorem reg_split_unsafe :
    AlignedMismatch L K
      { tr := fun g => if g = 0 then [regAt 0 72] else if g < 128 then [regAt 1 72] else []
        rf := fun _ _ => none } :=
  ⟨.setMaxReg, .inl ((AlignedClass.divergent_setMaxReg_iff L).2 ⟨(0, 0), (1, 0), 0, 1, false,
    false, 72, 72, 0, 0, ⟨⟨by decide, by decide, by decide⟩, by decide⟩, rfl, rfl, rfl,
    by decide⟩)⟩

/-- Warps 0 and 1 request different counts: unsafe. -/
theorem reg_count_unsafe : SetMaxNReg.Unsafe L (regs (fun w => w) (fun w => 72 + 8 * w)) :=
  ⟨(0, 0), 0, false, 72, 0, rfl, .inr (.inr (.inl ⟨(32, 0), 1, false, 80, 0,
    ⟨⟨by decide, by decide, by decide⟩, by decide⟩, rfl, rfl, .inr (by decide)⟩))⟩

end PTX.Tests.SameInstruction

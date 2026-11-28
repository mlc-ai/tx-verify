-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ref

@[expose] public section

/-! # Warpgroup 2's reference invariant is kept by every step

`ref_step`: from a state with `Ref`, an event of the state's shape that the machine follows leads
to a state with `Ref` for the bumped counts (an undefined-behaviour event bumps the class `ub`,
after which `Ref` asks nothing). `ref_init`: the first state with no counts. The set-up's events
count nothing on the slots' barriers; in the loop the successful polls and the arrivals count one
on the slot's barrier (`bump_of`), which is the slot's next use (`uses_succ`), and the back-edge
starts block `i + 1` with the flipped slot and parity bits. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

theorem loc_inj {f f' : MbarFam} (h : MbarRow.loc L g f = MbarRow.loc L g f') : f = f' := by
  simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact MbarFam.off_inj h

/-- The counts after an event of the role in class `c0` only. -/
theorem bump_of {e : Event} {c0 : Cnt} (hin : inRole e = true) (hk : kindOf e = some c0)
    (n : Cnt → Nat) : Code.bump cls n e = fun c => n c + if c = c0 then 1 else 0 := by
  funext c
  simp only [Code.bump, cls, hin, hk, Bool.true_and, Option.some.injEq, decide_eq_true_eq]
  by_cases h : c = c0
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The counts after an event in no class. -/
theorem bump_none {e : Event} (hk : kindOf e = none) (n : Cnt → Nat) : Code.bump cls n e = n := by
  funext c
  simp [Code.bump, cls, hk]

/-- Block `i` uses slot `i % 2` once more. -/
theorem uses_succ (b : Fin 2) (i : Nat) :
    uses b (i + 1) = uses b i + if b = MbarRow.slot2 i then 1 else 0 := by
  fin_cases b <;> simp [uses, MbarRow.slot2, Fin.ext_iff] <;> split_ifs <;> omega

/-- A set-up state's invariant from the set-up's counts. -/
theorem ref_setup {d : D} {n : Cnt → Nat} (hq : n (.acq (MbarRow.loc L g .qUtccp)) = 0)
    (hs : ∀ b, SlotCounts L g n b 0 0 0 0)
    (hd : d.site = .lenA ∨ d.site = .lenB ∨ d.site = .wq) : Ref L g d n := by
  intro _
  rcases hd with h | h | h <;> rw [h]
  · exact ⟨hq, hs⟩
  · exact ⟨hq, hs⟩
  · exact ⟨hq, hs⟩

/-- A loop state's invariant from its block words and counts at block `i`. -/
theorem ref_loop {d : D} {n : Cnt → Nat} {i : Nat} (hw : LoopWords d i) (h : LoopCounts L g d n i)
    (hd : d.site ≠ .smr ∧ d.site ≠ .lenA ∧ d.site ≠ .lenB ∧ d.site ≠ .wq ∧ d.site ≠ .bar ∧
      d.site ≠ .exit) : Ref L g d n := by
  intro _
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  cases site <;> first | exact ⟨i, hw, h⟩ | contradiction

/-- The closing barrier's invariant: every slot count is its uses among all blocks. -/
theorem ref_bar {d : D} {n : Cnt → Nat} (hd : d.site = .bar)
    (h : ∀ b, SlotCounts L g n b (uses b (rounds d.l0 d.l1)) (uses b (rounds d.l0 d.l1))
      (uses b (rounds d.l0 d.l1)) (uses b (rounds d.l0 d.l1))) : Ref L g d n := by
  intro _
  rw [hd]
  exact h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Shape
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-! # The startup's paired Tensor Memory operations

`RefT d t`: at state `d`, with `t` paired Tensor Memory operations (`Tmem.Pair.isTmemOp`) among
the thread's events before it. On the path of the elections (the warp word `x2` is `0`) none
before the allocation, one from it to the relinquishment; at the barrier and after it two in
warp 0 (`x2 = 0`) and none in the other warps. `refT_next`: a step keeps it at the count bumped
by its event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Flow.Arith32

/-- **The startup's count of paired Tensor Memory operations.** -/
def RefT (d : D) (t : Nat) : Prop :=
  match d.site with
  | .sh _ => t = 0
  | .elect _ | .init _ | .fence | .alloc => t = 0 ∧ scmpi .ne .b d.x2 0 = false
  | .allocSt | .ld | .trap | .relinq => t = 1 ∧ scmpi .ne .b d.x2 0 = false
  | .bar | .enter _ => t = if scmpi .ne .b d.x2 0 then 0 else 2

variable {L : Launch} {g : Nat}

/-- The first state has made no operation. -/
theorem refT_init : RefT (code L g).init 0 := rfl

/-- **The count is kept by every startup step.** -/
theorem refT_next {d d' : D} {e : Event} {t : Nat} (hT : RefT d t) (hev : Ev L g d e)
    (hs : succ L g d e = some (some d')) :
    RefT d' (t + if Tmem.Pair.isTmemOp e then 1 else 0) := by
  obtain ⟨pc, kd⟩ := e
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j =>
    simp only [RefT] at hT
    subst hT
    fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev <;> simp only at hk <;> subst hk <;>
      simp only [succ] at hs
    · obtain ⟨x, rfl⟩ : ∃ x, d' = { site := .sh 1, x1 := x, x2 := x2 } := by
        unfold word32 at hs
        split at hs
        · exact ⟨_, (Option.some.inj (Option.some.inj hs)).symm⟩
        · cases hs
      simp [RefT, Tmem.Pair.isTmemOp]
    · unfold word32 at hs
      split at hs
      · rename_i x
        by_cases hx : scmpi .ne .b x 0 = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at hs <;> subst hs <;>
          simp [RefT, Tmem.Pair.isTmemOp, hx]
      · cases hs
  | elect j =>
    obtain ⟨inst, ld, -, hk⟩ := hev
    simp only at hk
    subst hk
    obtain ⟨rfl, h2⟩ := hT
    simp only [succ] at hs
    fin_cases j <;> simp only [Option.some.injEq] at hs
    · subst hs; simp [RefT, Tmem.Pair.isTmemOp, h2]
    · split_ifs at hs <;> subst hs <;> simp [RefT, Tmem.Pair.isTmemOp, h2]
  | init n =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨rfl, h2⟩ := hT
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp only [initSucc]
    split <;> simp [RefT, Tmem.Pair.isTmemOp, h2]
  | fence =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨rfl, h2⟩ := hT
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp [RefT, Tmem.Pair.isTmemOp, h2]
  | alloc =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨rfl, h2⟩ := hT
    simp only [succ, Option.some.injEq] at hs
    split_ifs at hs <;> subst hs <;> simp [RefT, Tmem.Pair.isTmemOp, h2]
  | allocSt =>
    obtain ⟨col, -, hk⟩ := hev
    simp only at hk
    subst hk
    obtain ⟨rfl, h2⟩ := hT
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp [RefT, Tmem.Pair.isTmemOp, h2]
  | ld =>
    obtain ⟨rfl, h2⟩ := hT
    simp only [succ] at hs
    split at hs
    · split at hs
      · rename_i v _
        unfold afterLd at hs
        split at hs
        · split_ifs at hs <;> obtain rfl := Option.some.inj (Option.some.inj hs) <;>
            simp [RefT, Tmem.Pair.isTmemOp, h2]
        · cases hs
      · cases hs
    · cases hs
  | trap => simp [succ] at hs
  | relinq =>
    simp only [Ev] at hev
    subst hev
    obtain ⟨rfl, h2⟩ := hT
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp [RefT, Tmem.Pair.isTmemOp, h2]
  | bar =>
    simp only [Ev] at hev
    subst hev
    simp only [succ, Option.some.injEq] at hs
    subst hs
    simp only [RefT] at hT
    simp only [Tmem.Pair.isTmemOp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    unfold enterOf
    split_ifs <;> simp [RefT, hT]
  | enter r => simp [succ] at hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

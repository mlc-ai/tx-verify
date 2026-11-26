-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Time
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-! # The startup's warp collectives

A startup state has made `ncS` warp collectives: the shuffles at pcs 6 and 9, then, on warp 0 (the
recorded warp word `x2` is zero), the elections at pcs 16 and 31. A step adds one exactly when its
event is a collective (`ncS_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- Whether the recorded warp word is nonzero, as the code's comparison at pc 12 reads it. -/
def notWarp0 (x2 : BitVec 64) : Bool := scmpi .ne .b x2 0

/-- **The collectives a startup state has made.** -/
def ncS (d : D) : Nat :=
  match d.site with
  | .sh j => j.val
  | .elect j => 2 + j.val
  | _ => if notWarp0 d.x2 then 2 else 4

/-- Off the shuffles and elections the count is the warp's. -/
theorem ncS_other {d : D} (hs : ∀ j, d.site ≠ .sh j) (he : ∀ j, d.site ≠ .elect j) :
    ncS d = if notWarp0 d.x2 then 2 else 4 := by
  obtain ⟨site, x1, x2⟩ := d
  cases site <;> simp_all [ncS]

theorem enterOf_x2 (d : D) : (enterOf d).x2 = d.x2 := by
  unfold enterOf; split_ifs <;> rfl

theorem enterOf_sh (d : D) : ∀ j, (enterOf d).site ≠ .sh j := by
  unfold enterOf; split_ifs <;> simp

theorem enterOf_elect (d : D) : ∀ j, (enterOf d).site ≠ .elect j := by
  unfold enterOf; split_ifs <;> simp

variable {L : Launch} {g : Nat}

/-- **A startup step adds one collective exactly when its event is one.** -/
theorem ncS_step {d d' : D} {e : Event} (hev : Ev L g d e) (hu : ∀ f, e.kind ≠ .ub f)
    (hw : ∀ j, d.site = .elect j → notWarp0 d.x2 = false)
    (hs : succ L g d e = some (some d')) :
    ncS d' = ncS d + if Sched.isWarpColl e = true then 1 else 0 := by
  obtain ⟨site, x1, x2⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases site with
  | sh j =>
    fin_cases j
    · simp only [Ev] at hev
      obtain ⟨r, ok, rfl⟩ := hev
      simp only [succ, word32] at hs
      split at hs
      · cases hs; simp [ncS, Sched.isWarpColl]
      · simp at hs
    · simp only [Ev] at hev
      obtain ⟨r, ok, rfl⟩ := hev
      simp only [succ, word32] at hs
      split at hs
      · split at hs <;> cases hs <;> simp_all [ncS, Sched.isWarpColl, notWarp0]
      · simp at hs
  | elect j =>
    simp only [Ev] at hev
    obtain ⟨inst, ld, -, rfl⟩ := hev
    fin_cases j
    · simp only [succ] at hs; cases hs; simp [ncS, Sched.isWarpColl]
    · have h0 := hw 1 rfl
      simp only [notWarp0] at h0
      simp only [succ] at hs
      split at hs <;> cases hs <;> simp [ncS, Sched.isWarpColl, notWarp0, h0]
  | trap => simp only [succ] at hs; cases hs
  | enter r => simp only [succ] at hs; cases hs
  | init n =>
    simp only [Ev] at hev
    subst hev
    simp only [succ] at hs
    cases hs
    rw [ncS_other (by simp [initSucc]; split <;> simp) (by simp [initSucc]; split <;> simp),
      ncS_other (by simp) (by simp)]
    simp [Sched.isWarpColl]
  | fence =>
    simp only [Ev] at hev; subst hev; simp only [succ] at hs; cases hs
    rw [ncS_other (by simp) (by simp), ncS_other (by simp) (by simp)]; simp [Sched.isWarpColl]
  | alloc =>
    simp only [Ev] at hev; subst hev; simp only [succ] at hs
    split at hs <;> cases hs <;>
      (rw [ncS_other (by simp) (by simp), ncS_other (by simp) (by simp)]; simp [Sched.isWarpColl])
  | allocSt =>
    simp only [Ev] at hev
    obtain ⟨col, -, rfl⟩ := hev
    simp only [succ] at hs; cases hs
    rw [ncS_other (by simp) (by simp), ncS_other (by simp) (by simp)]; simp [Sched.isWarpColl]
  | ld =>
    simp only [Ev] at hev
    rcases hev with ⟨a, bs, rfl, -⟩ | ⟨f, hf⟩
    · simp only [succ] at hs
      split at hs
      · simp only [afterLd] at hs
        split at hs
        · split at hs <;> cases hs <;>
            (rw [ncS_other (by simp) (by simp), ncS_other (by simp) (by simp)];
             simp [Sched.isWarpColl])
        · cases hs
      · cases hs
    · exact absurd hf (hu f)
  | relinq =>
    simp only [Ev] at hev; subst hev; simp only [succ] at hs; cases hs
    rw [ncS_other (by simp) (by simp), ncS_other (by simp) (by simp)]; simp [Sched.isWarpColl]
  | bar =>
    simp only [Ev] at hev; subst hev; simp only [succ] at hs; cases hs
    rw [ncS_other (enterOf_sh _) (enterOf_elect _), ncS_other (by simp) (by simp), enterOf_x2]
    simp [Sched.isWarpColl]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

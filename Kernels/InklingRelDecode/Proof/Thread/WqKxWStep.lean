-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WqKxW

@[expose] public section

/-!
# The key time of the worker warps along steps

`kxW_silent`: a step from a silent state keeps the key time (the stretch ends at the same
synchronizing state). The closed forms of the key time after the loop's halves and iterations
(`kxM_afterQk`, `kxM_iterNext`, `kxL_afterIter`, `mmaT_start`) are used by the synchronizing steps
too.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g h : Nat} {e e' : Event}

/-! ### Closed forms -/

theorem kxM_iterNext (d : Mma.D) : kxM (Mma.iterNext d) = mmaT (Mma.iterNext d) := by
  unfold Mma.iterNext
  split_ifs <;> rfl

theorem kxM_afterQk (d : Mma.D) : kxM (Mma.afterQk d) = mmaT (Mma.afterQk d) := by
  unfold Mma.afterQk
  split_ifs
  · exact kxM_iterNext d
  · rfl

theorem kxL_afterIter (d : Loader.D) : kxL (Loader.afterIter d) =
    if d.n = (d.i + 1) % 2 ^ 32 then c2
    else loaderT { d with site := .wb0, i := d.i + 1 } := by
  simp only [Loader.afterIter]
  split <;> rfl

theorem mmaT_start (d : Mma.D) : mmaT (Mma.start d) =
    if d.n = 0 ∨ 2147483646 < d.n then epi0 - 100 else slot d.i + bandM + 0 := by
  unfold Mma.start
  split_ifs <;> rfl

theorem kxM_start (d : Mma.D) : kxM (Mma.start d) = mmaT (Mma.start d) := by
  unfold Mma.start
  split_ifs <;> rfl

/-! ### Silent steps -/

theorem ksilent_L {d d' : Loader.D} {P : Loader.Pro}
    (hn : Loader.next L g d e = some (some d')) (hs : wSy (.loader d P) = false) :
    kxL d' = kxL d := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub, Bool.or_false] at hs <;>
    first
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Loader.next, Loader.readI, Loader.readN] at hn
       (repeat' split at hn) <;>
         first
         | (simp at hn; done)
         | (simp only [Option.some.injEq] at hn
            subst hn
            first
            | rfl
            | (rw [kxL_afterIter]; rfl)))

theorem ksilent_M {d d' : Mma.D} {P : Loader.Pro}
    (hn : Mma.next L g d e = some (some d')) (hs : wSy (.mma d P) = false) :
    kxM d' = kxM d := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs <;>
    first
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Mma.next] at hn
       (repeat' split at hn) <;>
         first
         | (simp at hn; done)
         | (simp only [Option.some.injEq] at hn
            subst hn
            first
            | rfl
            | (rw [kxM_afterQk]; rfl)
            | (rw [kxM_iterNext]; rfl)
            | (simp only [Mma.qkNext, Mma.pvNext]; split <;> rfl)))

/-- **A step from a silent worker state keeps the key time.** -/
theorem kxW_silent {s t : WComp.WSt} (hn : WComp.next L g s e = some (some t))
    (hs : wSy s = false) : kxW t = kxW s := by
  cases s with
  | worker w =>
    obtain ⟨a, P⟩ := w
    cases a <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false,
        Bool.or_true] at hs <;>
      first
      | (exfalso; revert hs; decide +kernel)
      | (simp only [WComp.next, Worker.next] at hn
         (repeat' split at hn) <;>
           first
           | (simp at hn; done)
           | (simp only [Option.map_some, Option.some.injEq] at hn
              subst hn
              rfl))
  | idle d =>
    obtain ⟨a, P⟩ := d
    exfalso
    cases a <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs <;>
      (revert hs; decide +kernel)
  | loader d P =>
    have hl : d.site ≠ .setMaxInc := by
      obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      intro hw
      simp only at hw
      subst hw
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    rw [next_loader hl] at hn
    obtain ⟨d', hd', rfl⟩ := mapInv hn
    exact ksilent_L hd' hs
  | mma d P =>
    have hl : d.site ≠ .setMaxRegInc := by
      obtain ⟨s, i, n, tm, pro⟩ := d
      intro hw
      simp only at hw
      subst hw
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    rw [next_mma hl] at hn
    obtain ⟨d', hd', rfl⟩ := mapInv hn
    exact ksilent_M hd' hs
  | exit x =>
    obtain ⟨a, P⟩ := x
    cases a
    · exfalso
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    · simp [WComp.next] at hn

end
end PTX.Kernels.InklingRelDecode.Proof.Lk

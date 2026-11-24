-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtTime

@[expose] public section

/-!
# The virtual time rises along the softmax region's steps
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

/-- **Every counted step of the softmax region raises the time.** -/
theorem smT_lt {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some d')) (hc : e.counts = true) : smT d < smT d' := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> first
    | (simp only [Sm.next, Sm.afterSetup, Sm.afterArrive, Sm.D.afterSum, Sm.D.afterMax,
         Sm.D.afterMaxT] at h
       (repeat' split at h)
       all_goals (try simp only [Bound.Sm.toBar20_eq_some] at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try obtain ⟨-, rfl⟩ := h)
       all_goals (try (rw [Bound.counts_wait (by assumption)] at hc; contradiction))
       all_goals (try simp only [smT, Bound.Sm.pos, Sm.D.upd] at *)
       all_goals wt_omega)

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

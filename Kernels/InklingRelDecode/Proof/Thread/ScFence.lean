-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.FootOrder

@[expose] public section

/-!
# The prologue's copies come after its proxy fence

`ProA.Site.fnc0` is the `fence.proxy.async` the prologue executes after it initializes the
mbarriers, before its first tensor copy; the sites after it in the machine have larger positions,
and no step of the machine goes from a site at or before `fnc0` to a site after it except the
step from `fnc0` (`next_cross_fnc0`). So a state of the prologue that is past `fnc0` has the fence's
state earlier in its thread's run (`Interface.ScFence`), in particular every state at a copy site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- **No step goes past the fence except from it.** -/
theorem next_cross_fnc0 {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hs : s.pc ≤ Site.fnc0.pc)
    (hd : Site.fnc0.pc < d'.site.pc) : s = .fnc0 := by
  cases s <;> first
    | rfl
    | (exfalso; revert hs; decide +kernel)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            exfalso
            simp only at hd
            revert hd
            decide +kernel))

theorem qSite_pc_le (L : Launch) (g : Nat) (dt : Dat) (n : Nat) :
    (qSite L g dt n).pc ≤ Site.fnc1.pc := by
  unfold qSite
  split <;> (repeat' split) <;> decide +kernel

/-- **No step goes past the fence after the query stores except from it** (`fnc1`, the fence
before the role-table store). -/
theorem next_cross_fnc1 {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hs : s.pc ≤ Site.fnc1.pc)
    (hd : Site.fnc1.pc < d'.site.pc) : s = .fnc1 := by
  cases s <;> first
    | rfl
    | (exfalso; revert hs; decide +kernel)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            exfalso
            simp only at hd
            first
              | exact absurd hd (Nat.not_lt.mpr (qSite_pc_le _ _ _ _))
              | (revert hd; decide +kernel)))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA

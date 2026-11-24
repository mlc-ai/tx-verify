-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WnShape

@[expose] public section

/-!
# The lanes behind a lane at a warp collective, by synchronizing ordinal

The premise of `WarpCollFacts.lag`: lane `g` at a warp-collective state after `n` warp
collectives, a lane `h` of its warp with at most `n` of them, not at a warp-collective state after
exactly `n`. `lag_ordinal` gives what the lockstep says about `h`: it has made at most as many
synchronizing events as `g` (a lane with more has a synchronizing state of `g`'s ordinal, of `g`'s
key, so a warp collective it made after `n` others, `cnt_gt_of_ord`), and if as many, its state is
not synchronizing (it would have `g`'s key, so be at a warp collective after `n`). The time
comparison that `lag` asks for is not derived from this (row Wn2 of "thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wn
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
  (hA : LaneAgree Q L X)
include hX hf hA

/-- **The lockstep under the premise of `lag`**: the lane `h` has made at most as many
synchronizing events as `g`, and if as many, it is not at a synchronizing state. -/
theorem lag_ordinal {g h : Nat} {d : TSt} (hw : SameWarp L g h)
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hk : nextKind d = .warp)
    (hle : (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl)
    (hno : ¬ ((X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧
      ∃ d', St Q L X h (X.tr h).length = some (some d') ∧ nextKind d' = .warp)) :
    syN (kernelSkel Q L) X h (X.tr h).length ≤ syN (kernelSkel Q L) X g (X.tr g).length ∧
      (syN (kernelSkel Q L) X h (X.tr h).length = syN (kernelSkel Q L) X g (X.tr g).length →
        ∀ s', St Q L X h (X.tr h).length = some (some s') → ¬ (kernelSkel Q L).sy s') := by
  have hc : wcSt d = true := (nextKind_warp d).mp hk
  have e1 : cnt Sched.isWarpColl X g (X.tr g).length = (X.tr g).countP Sched.isWarpColl := by
    simp [cnt]
  have e2 : cnt Sched.isWarpColl X h (X.tr h).length = (X.tr h).countP Sched.isWarpColl := by
    simp [cnt]
  refine ⟨?_, ?_⟩
  · by_contra hgt
    push Not at hgt
    have := cnt_gt_of_ord hX hf hA hw le_rfl le_rfl hσ hc hgt
    omega
  · intro heq s' hs' hsy'
    have hL := lock_kernel hf.tracked hA
    have hkey := hL _ hw le_rfl le_rfl hσ hs' (wcSt_sy hc) hsy' rfl heq
    have hc' : wcSt s' = true := by rw [← wcKey_class hw (wcSt_sy hc) hsy' hkey]; exact hc
    have hev : ClassEv Sched.isWarpColl wcSt Q L X := fun {g k e s} hg he hσ =>
      isWarpColl_state hX hf hg he hσ
    have hcnt := lock_count (kernelSkel Q L) hf.tracked hL hev (fun hs => wcSt_sy hs)
      wcKey_class _ hw le_rfl le_rfl hσ hs' (wcSt_sy hc) hsy' rfl heq
    exact hno ⟨by omega, s', hs', (nextKind_warp s').mpr hc'⟩

end

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wn

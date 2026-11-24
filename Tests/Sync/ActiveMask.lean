-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Sync.WarpUniform

/-! `activemask` (§9.7.15.12): decoding, the rule, the event, the value it writes, and the
constraint `ActiveMaskOk` (DEP-WARP-ACTIVEMASK) on the mask returned: the bit of the executing lane
is set, the bit of a lane with no thread is clear, and the bits of the other lanes are
unconstrained. -/
namespace PTX.Tests.ActiveMask
open PTX.Syntax
noncomputable section

/-! ## Decoding and rules -/

-- `%r0` is register 0 (32-bit); `%p0` is register 1 (predicate).
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 1, 32⟩, ⟨"%p".toList, 1, 1⟩], labels := [], params := [] }

private def act : WarpInstr := { kind := .activemask, ty := some (.int .b 32), dsts := [some 0] }

example : Decode.op env "activemask.b32" [.register "%r0"] = .ok (.warp act) := rfl
example : act.rule = some .threadActivemask := rfl
-- "Destination d is a 32-bit destination register."
example : (Decode.op env "activemask.b32" [.register "%p0"]).isOk = false := rfl
-- `activemask` waits for no other lane, so its guard may differ between the lanes of a warp.
example : Op.uniform (.warp act) = false := rfl

/-! ## The event -/

private def launch : Launch := { grid := 1, block := 2, params := fun _ => none }

example : activemaskTmpl {} 0 =
    .activemask (fun r => next (setReg {} 0 (.bits 32 (r.setWidth 64)))) := rfl
example : eventTmpl [] launch 0 {} (.warp act) =
    .activemask (fun r => next (setReg {} 0 (.bits 32 (r.setWidth 64)))) := rfl
-- The mask returned is written to the destination as a 32-bit integer.
example : Fires 4 (activemaskTmpl {} 0) ⟨4, .activemask 3#32⟩
    (some (next (setReg {} 0 (.bits 32 3#64)))) := ⟨_, rfl, rfl⟩

/-! ## The mask returned

The threads 0 and 1 are lanes 0 and 1; each performs one `activemask`. -/

private def exec (tr : Nat → List Event) : Execution := { tr := tr, rf := fun _ _ => none }

/-- Lane 0 obtains `r0` and lane 1 obtains `r1`. -/
private def both (r0 r1 : BitVec 32) : Execution :=
  exec fun g => if g = 0 then [⟨0, .activemask r0⟩] else if g = 1 then [⟨0, .activemask r1⟩]
    else []

private theorem get_both {r0 r1 : BitVec 32} {h j pc : Nat} {k : Kind}
    (hj : (both r0 r1).get (h, j) = some ⟨pc, k⟩) :
    (h = 0 ∧ j = 0 ∧ k = .activemask r0) ∨ (h = 1 ∧ j = 0 ∧ k = .activemask r1) := by
  unfold both exec Execution.get at hj
  by_cases h0 : h = 0
  · subst h0; obtain _ | j := j <;> simp_all
  · by_cases h1 : h = 1
    · subst h1; obtain _ | j := j <;> simp_all
    · simp [h0, h1] at hj

private theorem both_iff (r0 r1 : BitVec 32) :
    ActiveMaskOk launch (both r0 r1) ↔
      (r0.getLsbD (laneOf launch 0) = true ∧ maskInWarp launch 0 r0.toNat) ∧
      (r1.getLsbD (laneOf launch 1) = true ∧ maskInWarp launch 1 r1.toNat) := by
  constructor
  · intro h
    exact ⟨h 0 0 0 r0 rfl, h 1 0 0 r1 rfl⟩
  · rintro ⟨h0, h1⟩ g i pc r hget
    rcases get_both hget with ⟨rfl, -, h⟩ | ⟨rfl, -, h⟩ <;>
      simp only [Kind.activemask.injEq] at h <;> subst h
    · exact h0
    · exact h1

-- Lane 0 sees mask 1 or 3: its own bit is set, and the bit of lane 1 is unconstrained.
theorem mask1_ok : ActiveMaskOk launch (both 1#32 3#32) :=
  (both_iff _ _).2 ⟨⟨by decide, by decide⟩, by decide, by decide⟩
theorem mask3_ok : ActiveMaskOk launch (both 3#32 3#32) :=
  (both_iff _ _).2 ⟨⟨by decide, by decide⟩, by decide, by decide⟩
-- Lane 1 sees mask 2: the bit of lane 0 is clear.
theorem mask2_lane1_ok : ActiveMaskOk launch (both 1#32 2#32) :=
  (both_iff _ _).2 ⟨⟨by decide, by decide⟩, by decide, by decide⟩
-- The executing lane is active, so mask 2 is not possible for lane 0.
theorem own_bit_clear : ¬ ActiveMaskOk launch (both 2#32 3#32) :=
  fun h => absurd ((both_iff _ _).1 h).1.1 (by decide)
theorem own_bit_clear_lane1 : ¬ ActiveMaskOk launch (both 3#32 1#32) :=
  fun h => absurd ((both_iff _ _).1 h).2.1 (by decide)
-- A lane with no thread is never active.
theorem no_thread_4 : ¬ ActiveMaskOk launch (both 4#32 3#32) :=
  fun h => absurd ((both_iff _ _).1 h).1.2 (by decide)
theorem no_thread_7 : ¬ ActiveMaskOk launch (both 7#32 3#32) :=
  fun h => absurd ((both_iff _ _).1 h).1.2 (by decide)

end
end PTX.Tests.ActiveMask

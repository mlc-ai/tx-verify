-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtBar0Lock

@[expose] public section

/-!
# `RegWaitFacts.exit`: a lane exits only after every request of its warp

A lane `h` of the warp of a request `e` (ordinal `ρ`) that has exited has made more than `ρ`
requests: otherwise `h` is a participant that exits having executed at most `ρ` requests while
another participant executes its `ρ`-th (`AlignedClass.Exited` for `setmaxnreg`, whose participants
are the warpgroup, so a fortiori the warp), and the execution is unsafe. So `h` has a request of
ordinal `ρ`.

The statement needs the safety of the execution (`¬ Unsafe`): `Remaining.regWaits` takes a
consistent execution only, so the field is proved with this extra premise (a row in
the development notes).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A safe execution has no aligned mismatch of the `setmaxnreg` class. -/
theorem not_regExited (hs : ¬ Unsafe L kernel asms mem0 X) :
    ¬ AlignedClass.setMaxReg.Exited L kernel X := fun h =>
  hs (by
    right; right; right; right; right; right; right; right; left
    exact ⟨.setMaxReg, Or.inr h⟩)

/-- **`RegWaitFacts.exit`**: a lane exits only after every request of a lane of its warp. -/
theorem reg_exit (hs : ¬ Unsafe L kernel asms mem0 X) {e : EvId} {pc n inst : Nat} {inc : Bool}
    (hr : SetMaxNReg.Request X e pc inc n inst) {h j pc' : Nat} (hw : SameWarp L e.1 h)
    (hx : X.get (h, j) = some ⟨pc', .exit⟩) :
    ∃ j' pc'' inc' n' inst', SetMaxNReg.Request X (h, j') pc'' inc' n' inst' ∧
      SetMaxNReg.ordinal X (h, j') = SetMaxNReg.ordinal X e := by
  have hnot := not_regExited hs
  have hgt : SetMaxNReg.ordinal X e < (X.tr h).countP SetMaxNReg.isRequest := by
    by_contra hle
    apply hnot
    refine ⟨e, (h, j), ⟨pc, .setMaxReg inc n inst⟩, ?_, hr, rfl, rfl, ⟨pc', hx⟩, ?_⟩
    · obtain ⟨⟨hc1, hc2, hc3⟩, hwp⟩ := hw
      refine ⟨⟨hc1, hc2, hc3⟩, ?_⟩
      simp only at hwp ⊢
      omega
    · show (X.tr h).countP SetMaxNReg.isRequest ≤ ((X.tr e.1).take e.2).countP _
      exact Nat.le_of_not_lt hle
  obtain ⟨j', ev, hj', hev, hjo⟩ := NamedBar.exists_ordinal SetMaxNReg.isRequest (X.tr h) hgt
  obtain ⟨pcx, kd⟩ := ev
  cases kd <;> simp [SetMaxNReg.isRequest] at hev
  rename_i inc' n' inst'
  exact ⟨j', pcx, inc', n', inst', hj', hjo⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

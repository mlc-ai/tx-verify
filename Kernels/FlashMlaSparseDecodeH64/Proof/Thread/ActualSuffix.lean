-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The concrete remainder of a thread from a followed state -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Split a concrete thread run before a suffix that contains an event. -/
theorem run_split_nonempty {t : TState} {before tail : List Event} {o : Option TState}
    (hRun : Run kernel Assumptions.all L g t (before ++ tail) o) (hTail : tail ≠ []) :
    ∃ u, Run kernel Assumptions.all L g t before (some u) ∧
      Run kernel Assumptions.all L g u tail o := by
  induction before generalizing t with
  | nil => exact ⟨t, .nil _, hRun⟩
  | cons e es ih =>
    change Run kernel Assumptions.all L g t (e :: (es ++ tail)) o at hRun
    generalize hList : e :: (es ++ tail) = events at hRun
    cases hRun with
    | nil => cases hList
    | step hReach he hRest =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hList
      obtain ⟨u, hBefore, hAfter⟩ := ih hRest
      exact ⟨u, .step hReach he hBefore, hAfter⟩
    | last =>
      have hNil := (List.append_eq_nil_iff.mp (List.cons.inj hList).2).2
      exact (hTail hNil).elim

/-- At a followed point in an actual execution, recover the concrete composed state and
the entire remaining trace. No later state of the whole-thread frame is required. -/
theorem actual_suffix_from_followed {X : Execution} {d : Machine.ThreadD} {i : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.code P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hNonempty : (X.tr g).drop i ≠ []) :
    ∃ u o, (Machine.code P L g).Good (some d) u ∧
      Run kernel Assumptions.all L g u ((X.tr g).drop i) o := by
  obtain ⟨o, hRun⟩ := hX.thr g hg
  have hDecomp : X.tr g = (X.tr g).take i ++ (X.tr g).drop i :=
    (List.take_append_drop ..).symm
  rw [hDecomp] at hRun
  obtain ⟨t, hPrefix, hTail⟩ := run_split_nonempty hRun hNonempty
  have hReach : (Machine.code P L g).toMachine.Reach (some d) t := by
    have hFinal := hs.machine.final hPrefix
    change (Machine.code P L g).toMachine.after (Machine.code P L g).toMachine.init
      ((X.tr g).take i) = some (some d) at hd
    rw [hd] at hFinal
    rcases hFinal with ⟨_, hEq, hReach⟩ | hBad
    · cases hEq
      exact hReach
    · cases hBad
  generalize hList : (X.tr g).drop i = rest at hTail
  cases hTail with
  | nil => exact (hNonempty hList).elim
  | step hTau hEvent hr =>
    refine ⟨_, o, hReach _ hTau (stops_of_estep hEvent), ?_⟩
    exact .step .refl hEvent hr
  | last hTau hEvent =>
    refine ⟨_, none, hReach _ hTau (stops_of_estep hEvent), ?_⟩
    exact .last .refl hEvent

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

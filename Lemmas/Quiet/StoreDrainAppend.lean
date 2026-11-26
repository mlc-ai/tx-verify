-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.StoreDrain
public import Lemmas.Step.WarpAppend

@[expose] public section

/-! # Appending events to several drained threads keeps the drain constraint

`TensorStore.ReadsDrainedBeforeExit.snoc` for `Execution.appendLanes`: an appended exit is
harmless when its thread's selected stores have finished reading (`TensorStore.Drained`); events
that are no exit add no requirement. -/

namespace PTX
open PTX.Step

variable {select : Nat → Bool} {X : Execution} {ds : List Nat} {ev : Nat → Event}

/-- **Appending one event to each lane of `ds` keeps the drain constraint** when the lanes that
get an exit are drained. -/
theorem TensorStore.ReadsDrainedBeforeExit.appendLanes
    (h : TensorStore.ReadsDrainedBeforeExit select X)
    (hnew : ∀ g ∈ ds, (ev g).kind = .exit → TensorStore.Drained select X g) :
    TensorStore.ReadsDrainedBeforeExit select (X.appendLanes ds ev) := by
  intro i finish hb ⟨site, address, spec, hi, hsite⟩ ⟨pc, he⟩
  have hlen : i.2 < (X.tr i.1).length := by
    have h1 := hb.2.1
    have h2 := hb.2.2
    rw [← hb.1] at h2
    rw [appendLanes_len] at h2
    split_ifs at h2 <;> omega
  rw [appendLanes_get_old hlen] at hi
  change X.AsyncPresent i .readsDone
  rcases appendLanes_get_cases he with ⟨-, heX⟩ | ⟨hfd, -, hk⟩
  · exact h ⟨hb.1, hb.2.1, len_of_get heX⟩ ⟨site, address, spec, hi, hsite⟩ ⟨pc, heX⟩
  · have hkx : (ev finish.1).kind = .exit := by rw [← hk]
    exact hnew finish.1 hfd hkx i hb.1 ⟨site, address, spec, hi, hsite⟩

end PTX

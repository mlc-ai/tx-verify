-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Lemmas.Kernel.PostEvent

@[expose] public section

/-! # The state before the last event of a run is a state of the lane -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

variable {L : Launch} {g : Nat}

/-- The state before an event is a state of the lane. -/
theorem lane_pre {X : Execution} {k : Nat} {e : Event} {t : TState}
    (hk : (X.tr g)[k]? = some e)
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1)) (some t)) :
    ∃ s, Iface.LaneState L X g s ∧ EStep kernel Assumptions.all L g s e (some t) := by
  rw [List.take_add_one, hk, Option.toList_some] at hr
  obtain ⟨u, s, hu, hus, hes⟩ := Run.unsnoc _ e hr
  exact ⟨s, ⟨k, u, hu, hus⟩, hes⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib

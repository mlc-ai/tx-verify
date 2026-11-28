-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX

variable {X : Execution} {g : Nat}

/-- The barrier-0 count of a thread before position `k`. -/
abbrev c0 (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP (Execution.isBarId 0)

theorem c0_mono {k j : Nat} (h : k ≤ j) : c0 X g k ≤ c0 X g j :=
  (List.take_sublist_take_left h).countP_le

theorem c0_succ {k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) :
    c0 X g (k + 1) = c0 X g k + if Execution.isBarId 0 e then 1 else 0 := by
  unfold c0
  rw [List.take_add_one, he, Option.toList_some, List.countP_append]
  by_cases hb : Execution.isBarId 0 e <;> simp [hb]

end PTX.Kernels.InklingRelDecode.Proof

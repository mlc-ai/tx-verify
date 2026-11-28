-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.PcStep

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

/-- No assumption of the kernel selects a segment at a program counter outside the software
`exp2` instances. -/
theorem segFree {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc Assumptions.all pc := by
  intro a ha L g t htpc
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · rfl
  · show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then _ else none) = none
    rw [htpc, h]
    simp
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof

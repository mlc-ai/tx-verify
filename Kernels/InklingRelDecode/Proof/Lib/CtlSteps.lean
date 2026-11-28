-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.Havoc
public import Kernels.InklingRelDecode.Proof.Lib.Segments
public import Lemmas.Flow.SegCtl
public import Lemmas.Flow.BranchJoinU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

theorem bra_rule {L : Launch} {g target : Nat} {uni : Bool} (t : TState) (a : Assumption)
    (ha : a ∈ Assumptions.all) : a.localRule L g t (.bra target uni) = none := by
  simp only [Assumptions.all,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try rfl
  all_goals simp [Assumptions.lg2Exact,Assumptions.divFullExact,Assumptions.negExact]

macro "ink_ctl" : tactic => `(tactic| seg_ctl rulesFrame, hooks_ok)

end PTX.Kernels.InklingRelDecode.Proof.Lib

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.StepsPaths

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

theorem inv_next {L g d dn ev} (hi : Inv d) (move : next L g d ev=some (some dn)) : Inv dn := by
  obtain ⟨s,i,v⟩ := d
  cases s
  case ldNum =>
    simp only [next] at move
    split at move <;> try contradiction
    rename_i bs _
    cases h : (rebuild 3 bs).toOption <;> simp [h] at move
    cases move
    exact hi
  all_goals simp only [next,issueNext,startSite] at move
  all_goals repeat' split at move
  all_goals cases move
  all_goals first | trivial | exact inv_after hi.1 hi.2 | exact inv_iter hi.2.1 hi.2.2 |
    (simp_all [Inv,D.limit]; omega)

end PTX.Kernels.InklingRelDecode.Proof.Mma

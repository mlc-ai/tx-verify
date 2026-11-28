-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

theorem inv_next {L g d dn ev} (move : next L g d ev=some (some dn)) :
    dn.site=.arrive → laneOf L g=0 := by
  obtain ⟨s,i,l,p,q⟩ := d
  cases s
  case' page b => cases b
  case' copy j b => cases b
  all_goals simp only [next,finishPair] at move
  all_goals repeat' split at move
  all_goals try contradiction
  all_goals first | (obtain ⟨_,_,_,_,_,rfl⟩ := read_next move; nofun) |
    (cases move; all_goals simp_all)

end PTX.Kernels.InklingRelDecode.Proof.Loader

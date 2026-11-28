-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open Control

def needsPrevious : Site → Bool
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL
  | .shfl11 | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO => true
  | _ => false

private theorem loop_early (e t i) : needsPrevious (loopSite e t i)=false := by
  unfold loopSite; split_ifs <;> rfl

theorem previous_next {ent L g d ev dn}
    (before : needsPrevious d.site=true → 0<d.i)
    (step : Control.next ent L g d ev=some (some dn)) : needsPrevious dn.site=true → 0<dn.i := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals dsimp only
  all_goals first | exact before | exact fun _ => before rfl | (intro h; cases h; done) |
    (rw [loop_early]; simp) | (intro; omega)

end PTX.Kernels.InklingRelDecode.Proof.Softmax

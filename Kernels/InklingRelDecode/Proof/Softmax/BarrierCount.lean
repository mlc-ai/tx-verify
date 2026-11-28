-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open Control

/-- Count the four fixed rendezvous, independently of the optional O rescale
at 2326. The first iteration omits 2241 and 2251. -/
def fixedSync (pc : Nat) := pc==2241 || pc==2251 || pc==999 || pc==1012

/-- Twice-offset count of fixed rendezvous since the Softmax handoff. The
offset provides the two omitted barriers of the first iteration. -/
def syncPosition (s : Site) (i : Nat) : Nat :=
  match s with
  | .waitO | .bar22 => 0
  | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 => 1
  | .ldL | .shfl11 | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO | .bar20 => 2
  | .tmemSt | .tmemWait | .bar21 => 3
  | .arrive => 4
  | _ => if i=0 then 2 else 0

def fixedCount (d : D) := 4*d.i+syncPosition d.site d.i

private theorem loop_pos (e t i) : syncPosition (loopSite e t i) i=(if i=0 then 2 else 0) := by
  unfold loopSite
  split <;> first | rfl | (split <;> rfl)

private theorem fixed_sites (s : Site) : fixedSync s.pc =
    (match s with | .bar20 | .bar21 | .bar22 | .bar23 => true | _ => false) := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem fixed_next {ent L g d ev dn} (step : Control.next ent L g d ev=some (some dn)) :
    fixedCount dn = fixedCount d + (fixedSync d.site.pc).toNat := by
  rw [fixed_sites]
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp only [fixedCount]
  all_goals try rw [loop_pos]
  all_goals simp only [syncPosition,Bool.toNat_true,Bool.toNat_false,
    Nat.add_zero,Nat.add_one_ne_zero,ite_false]
  all_goals first | rfl | omega | (split <;> omega)

end PTX.Kernels.InklingRelDecode.Proof.Softmax

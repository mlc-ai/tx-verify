-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.ScratchIteration
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open Control

/-- The sites whose event is a warp shuffle. -/
def Site.isShuffle : Site → Bool
  | .shfl4 | .shfl5 | .shfl6 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .shfl11 | .shfl12 => true
  | _ => false

/-- Shuffles of round `i` done before the site. -/
def shflInRound (s : Site) (i : Nat) : Nat :=
  match s with
  | .shfl4 => 0
  | .ldS | .waitLd | .shfl5 => 1
  | .shfl6 => 2
  | .waitO | .bar22 | .shfl7 => 3
  | .shfl8 => 4
  | .shfl9 => 5
  | .shfl10 => 6
  | .store10 | .bar23 | .ldL | .shfl11 => 7
  | .shfl12 => 8
  | .ldO | .waitLdO | .bar24 | .stO | .waitStO | .bar20 | .tmemSt | .tmemWait | .bar21
  | .arrive => if i=0 then 3 else 9
  | _ => 0

/-- The shuffles done since the Softmax handoff. -/
def shflCount (d : D) : Nat := Lib.shflBase d.i+shflInRound d.site d.i

private theorem loop_in (e t i) : shflInRound (loopSite e t i) i=0 := by
  unfold loopSite
  split <;> first | rfl | (split <;> rfl)

theorem shfl_next {ent L g d ev dn} (before : needsPrevious d.site=true → 0<d.i)
    (step : Control.next ent L g d ev=some (some dn)) :
    shflCount dn=shflCount d+d.site.isShuffle.toNat := by
  obtain ⟨s,i,v⟩ := d
  have pos : needsPrevious s=true → 0 < i := before
  cases s <;> simp only [Control.next,advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp only [shflCount,Site.isShuffle]
  all_goals try rw [loop_in]
  all_goals simp only [shflInRound,Lib.shflBase,Bool.toNat_true,Bool.toNat_false,Nat.add_zero,
    Nat.add_one_ne_zero,ite_false]
  all_goals first | omega | (split <;> omega) | (have := pos rfl; split <;> omega)

set_option maxRecDepth 10000 in
/-- The loop leaves for the epilogue only at its limit. -/
theorem epilogue_limit {ent L g d ev dn}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.epilogue) :
    dn.i=ent.limit := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | assumption | (simp at site)

end PTX.Kernels.InklingRelDecode.Proof.Softmax

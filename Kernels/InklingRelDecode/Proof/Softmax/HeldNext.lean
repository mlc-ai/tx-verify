-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.TcCount

@[expose] public section

/-! # The broadcast word of a Softmax thread

The warp broadcast at pc 1261 is received at the site `shfl4` and held while the round runs, from
the S load on (`Softmax.held`). A step either receives it, or keeps it with the round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open _root_.PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

/-- The sites that hold the round's broadcast word: the S load and the sites after it. -/
def held : Site → Bool
  | .ldS => true
  | s => afterLdS s

private theorem loop_held (e t i) : held (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

set_option maxRecDepth 10000 in
/-- A step into a site that holds the word receives the broadcast, or comes from a site that
holds it in the same round. -/
theorem held_next {ent L g d ev dn} (step : Control.next ent L g d ev = some (some dn))
    (hd : held dn.site = true) :
    (d.site = .shfl4 ∧ dn.i = d.i ∧ ∃ m a b c ok, ev.kind = .shfl m a b c dn.held.base ok) ∨
    (held d.site = true ∧ dn.i = d.i ∧ dn.held.base = d.held.base) := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first
    | (simp only [loop_held] at hd; cases hd; done)
    | (simp only [held,afterLdS] at hd ⊢; try (simp; done))
  exact Or.inl ⟨trivial,trivial,_,_,_,_,_,by assumption⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax

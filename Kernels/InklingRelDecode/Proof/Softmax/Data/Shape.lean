-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Machine

@[expose] public section

/-! # Where the round's sites sit in the control machine's successor

The round's sites (`inRound`) lead to each other and to `bar20` only, `bar20` from the three sites
the words are updated at; the shuffle of pc 1838 leads into the round; the sites before the loop
(`early`) have no successor outside them but the loop's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

/-- The sites before the loop. -/
def early : Site → Bool
  | .setMaxReg | .bar0 | .pre _ => true
  | _ => false

private theorem loop_round (e : Entry) (t i : Nat) : inRound (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

private theorem loop_early (e : Entry) (t i : Nat) : early (loopSite e t i) = false := by
  unfold loopSite; split <;> first | rfl | (split <;> rfl)

/-- **The successor of a control state** keeps the round's sites together. -/
theorem next_shape {e : Entry} {L : Launch} {g : Nat} {d dn : Control.D} {ev : Event}
    (step : Control.next e L g d ev = some (some dn)) :
    (d.site = .shfl5 → dn.site = .shfl6) ∧
    (d.site ≠ .shfl5 → inRound d.site = false → inRound dn.site = false) ∧
    (inRound d.site = true → inRound dn.site = true ∨
      (dn.site = .bar20 ∧ (d.site = .shfl6 ∨ d.site = .shfl12 ∨ d.site = .waitStO))) ∧
    (early dn.site = true → early d.site = true) := by
  obtain ⟨s, i, v⟩ := d
  cases s <;> simp only [Control.next, advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals dsimp only
  all_goals (try simp only [loop_round, loop_early]); all_goals simp_all [inRound, early]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

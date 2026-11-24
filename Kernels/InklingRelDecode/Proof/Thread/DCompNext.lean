-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompBase

@[expose] public section

/-!
# The default-partition thread machine: what the successors preserve and the bridge's end

* `next_pro`: a prologue successor keeps the inherited registers (`dt.pro`), so the composed
  invariant's `d.dt.pro = DStart.inh L g Q tm` survives every prologue event; it is what lets the
  prologue's last event meet the softmax region's entry premises (`w71`, `%p3`, the base word).
* `dead_of_rtg`: a state whose local steps reach a dead state is dead (the bridge's float steps).
* `inv_epiStart`: the epilogue's invariant at the first state of the normal path holds when the
  numbers are in range (the premises of `Epi.start` other than the entry facts are not needed
  for the invariant).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A prologue successor keeps the inherited registers. -/
theorem next_pro {L : Launch} {g : Nat} {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) : d'.dt.pro = d.dt.pro := by
  unfold ProA.next at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; first | rfl | (split <;> rfl))
    | (dsimp only at h
       split at h
       all_goals first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h; subst h; split <;> rfl))

/-- The prologue's own successor keeps the base word. -/
theorem next_w {L : Launch} {g : Nat} {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) : d'.dt.w = d.dt.w := by
  unfold ProA.next at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; first | rfl | (split <;> rfl))
    | (dsimp only at h
       split at h
       all_goals first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h; subst h; split <;> rfl))

/-- A state whose local steps reach a dead state is dead. -/
theorem dead_of_rtg {L : Launch} {g : Nat} {u t : TState}
    (hr : Relation.ReflTransGen (Tau kernel asms L g) u t)
    (hd : Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) :
    Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hd
  | head h _ ih => exact Machine.dead_of_tau h ih

end
end PTX.Kernels.InklingRelDecode.Proof.DComp

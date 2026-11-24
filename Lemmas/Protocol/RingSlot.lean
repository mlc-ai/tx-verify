-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # Ring slots as data

A proof tool. A ring slot has `nf` full objects, which producers fill and consumers poll (consumer
`b` polls full object `owner b`), and one empty object per producer, which consumers' notifications
complete and that producer polls. Which threads produce and consume, and which records are a
consumer's notification to a producer, are parameters of the slot. This is data only: the
protocols read each object through its own history (`MbarRing.Round.Slot`). -/

namespace PTX.MbarRing

open AsyncCopy MBarrier

/-- A ring slot with `np` producers, `nc` consumers and `nf` full objects. -/
structure RingSlot (np nc nf : Nat) where
  full : Fin nf → Loc
  empty : Fin np → Loc
  owner : Fin nc → Fin nf
  producer : Fin np → Nat → Bool
  consumer : Fin nc → Nat → Bool
  notification : Fin np → Fin nc → Record Ref → Bool

namespace RingSlot

variable {np nc nf : Nat} (S : RingSlot np nc nf)

/-- The slot's objects. -/
def objects : Finset Loc := Finset.univ.image S.full ∪ Finset.univ.image S.empty

theorem full_mem (k : Fin nf) : S.full k ∈ S.objects :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

theorem empty_mem (a : Fin np) : S.empty a ∈ S.objects :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))

theorem objects_cases {m : Loc} (hm : m ∈ S.objects) :
    (∃ k, m = S.full k) ∨ ∃ a, m = S.empty a := by
  simp only [objects, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hm
  rcases hm with ⟨k, h⟩ | ⟨a, h⟩
  · exact .inl ⟨k, h.symm⟩
  · exact .inr ⟨a, h.symm⟩

/-- The slot's objects are distinct. -/
structure Distinct : Prop where
  full_ne : ∀ k a, S.full k ≠ S.empty a
  full_inj : Function.Injective S.full
  empty_inj : Function.Injective S.empty

/-- The facts of a family of ring slots that the layers above the ring protocols use: every
record of a slot's objects is fault-free. -/
structure Facts {ι : Type} (slots : ι → RingSlot np nc nf) (X : Execution) : Prop where
  fault_free : ∀ {i : ι} {m : Loc}, m ∈ (slots i).objects → ∀ r ∈ X.objects m, r.fault = none

end RingSlot

end PTX.MbarRing

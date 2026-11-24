-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Roles
public import Lemmas.Kernel.Counted
public import Lemmas.Kernel.UbLast
public import Lemmas.Kernel.Followed

@[expose] public section

/-! # The thread frame of a counted machine family, and the assembly of the roles' following

A proof tool, generic over the kernel (the kernel-independent part of the tml-fa4 thread frame,
`Proof2/Common/Frame.lean` and `Proof2/Common/Migrated.lean`). For a family of counted machines
(`Code.counted`, such as `Code.roleThread`):

* `count_all`: the count of a class that holds of every event is the position in the trace;
* `ub_zero`: a state before an event has counted no undefined behaviour (an undefined-behaviour
  event is its thread's last, `ub_last`), so a reference invariant may be guarded by "no
  undefined behaviour so far" at no cost;
* `followedAt_sel`: the following of every thread with the reference invariant of the role its
  thread index selects (`J (sel g) g`) is the following of each thread with its own role's
  invariant. A kernel proves its roles one at a time (`good` per role, on the lanes of the role's
  warps) and assembles them by cases on the thread index, as tml-fa4's `good_migrated`. -/

namespace PTX.Frame
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {g k : Nat} {κ : Type}

/-- **The count of a class that holds of every event is the position**, within the trace. -/
theorem count_all {C : (g : Nat) → Code K A L g} {cls : Nat → κ → Event → Bool} {c : κ}
    (hall : ∀ e, cls g c e = true) {dn : ((C g).counted (cls g)).D}
    (h : stateAt (fun g => (C g).counted (cls g)) X g k = some (some dn))
    (hk : k ≤ (X.tr g).length) : dn.2 c = k := by
  rw [count_eq h c, List.countP_eq_length.mpr (fun e _ => hall e), List.length_take,
    Nat.min_eq_left hk]

/-- **A state before an event has counted no undefined behaviour**: an undefined-behaviour event
is its thread's last. -/
theorem ub_zero {C : (g : Nat) → Code K A L g} {cls : Nat → κ → Event → Bool} {c : κ}
    (hX : Consistent L K A mem0 X) (hub : ∀ e, cls g c e = true → ∃ pc f, e = ⟨pc, .ub f⟩)
    {e : Event} (he : X.get (g, k) = some e) {dn : ((C g).counted (cls g)).D}
    (h : stateAt (fun g => (C g).counted (cls g)) X g k = some (some dn)) : dn.2 c = 0 := by
  by_contra h0
  obtain ⟨j, hj, f, hf, hc⟩ := exists_of_count h (Nat.pos_of_ne_zero h0)
  obtain ⟨pc, fl, rfl⟩ := hub f hc
  have := ub_last hX hf he
  omega

/-- **The roles' following, assembled**: each thread followed with the invariant of the role its
index selects is the family followed with the selected invariants. -/
theorem followedAt_sel {C : (g : Nat) → Code K A L g} {ρ : Type} (sel : Nat → ρ)
    {J : ρ → ∀ g, (C g).D → Prop} :
    FollowedAt C (J (sel g)) X g k ↔ FollowedAt C (fun h => J (sel h) h) X g k :=
  Iff.rfl

end
end PTX.Frame

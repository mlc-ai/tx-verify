-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane

@[expose] public section

/-! # No undefined behaviour in a lane's prefix

`NoUbBefore X x K`: none of the first `K` events of lane `x` is undefined behaviour. It holds for
the events before any event of the lane (`noUbBefore_of_get`: an undefined-behaviour event is the
thread's last), so a fact about a lane's states up to an event needs no global hypothesis. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- **The first `K` events of lane `x` are no undefined behaviour.** -/
def NoUbBefore (X : Execution) (x K : Nat) : Prop :=
  ∀ j < K, ∀ pc fl, X.get (x, j) ≠ some ⟨pc, .ub fl⟩

theorem noUbBefore_of_noUb (h : ¬ HasUb X) {K : Nat} : NoUbBefore X x K :=
  fun j _ pc fl hg => h ⟨(x, j), pc, fl, hg⟩

theorem noUb_kind (hnu : ¬ HasUb X) {k : Nat} {e : Event} (he : X.get (x, k) = some e) :
    ∀ f, e.kind ≠ .ub f := fun f hf => by
  obtain ⟨pc, kd⟩ := e
  simp only at hf
  subst hf
  exact hnu ⟨_, _, _, he⟩

theorem NoUbBefore.mono {K K' : Nat} (h : NoUbBefore X x K) (hk : K' ≤ K) : NoUbBefore X x K' :=
  fun j hj => h j (by omega)

/-- The event at a position below the bound is no undefined behaviour. -/
theorem NoUbBefore.ne {K j : Nat} {e : Event} (h : NoUbBefore X x K) (hj : j < K)
    (he : X.get (x, j) = some e) : ∀ f, e.kind ≠ .ub f := fun f hf =>
  h j hj e.pc f (by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf])

/-- **No event before a lane's event is undefined behaviour** (it would be the lane's last). -/
theorem noUbBefore_of_get (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {e : Event}
    (he : X.get (x, k) = some e) : NoUbBefore X x k := by
  intro j hj pc fl hg
  have h0 := take_noUb_of (c := fun f : Event => match f.kind with | .ub _ => true | _ => false)
    (fun f hf => by
      obtain ⟨pc, kd⟩ := f
      cases kd <;> simp at hf
      exact ⟨_, rfl⟩) hX he
  have hmem : (⟨pc, .ub fl⟩ : Event) ∈ (X.tr x).take k := by
    refine List.mem_iff_getElem?.mpr ⟨j, ?_⟩
    rw [List.getElem?_take_of_lt hj]
    exact hg
  exact (List.countP_eq_zero.mp h0) _ hmem rfl

/-- **No lane of warps 0 to 3 has an undefined-behaviour event**: what the startup's and
warpgroup 0's leaves give. The facts about warpgroup 0's lanes (`Common/Wg0*`) need no more of
`¬ HasUb X`. -/
def NoUbWg0 (L : Launch) (X : Execution) : Prop :=
  ∀ y, MbarRow.warp L y < 4 → ∀ j pc fl, X.get (y, j) ≠ some ⟨pc, .ub fl⟩

theorem noUbWg0_of_noUb (L : Launch) (h : ¬ HasUb X) : NoUbWg0 L X :=
  fun _ _ j pc fl hg => h ⟨(_, j), pc, fl, hg⟩

/-- **No event of warps 0 to 3 that has a successor in its lane is undefined behaviour**: the
part of `NoUbWg0` a consistent execution has (`noUbInner`); the last event's kind is the claim's
own. -/
def NoUbInner (L : Launch) (X : Execution) : Prop :=
  ∀ y, MbarRow.warp L y < 4 → ∀ j pc fl, j + 1 < (X.tr y).length →
    X.get (y, j) ≠ some ⟨pc, .ub fl⟩

theorem NoUbWg0.inner {L : Launch} (h : NoUbWg0 L X) : NoUbInner L X :=
  fun y hy j pc fl _ => h y hy j pc fl

theorem noUbInner {L : Launch} {m : Mem0} (hX : Consistent L kernel Assumptions.all m X) :
    NoUbInner L X := fun y _ j pc fl hj hg =>
  noUbBefore_of_get hX (k := j + 1) (x := y) (e := (X.tr y)[j + 1])
    (List.getElem?_eq_getElem hj) j (Nat.lt_succ_self _) pc fl hg

/-- A global absence of undefined behaviour is used where the warps 0 to 3's is asked for. -/
instance (L : Launch) (h : ¬ HasUb X) : CoeDep (¬ HasUb X) h (NoUbWg0 L X) :=
  ⟨noUbWg0_of_noUb L h⟩

instance (L : Launch) (h : ¬ HasUb X) : CoeDep (¬ HasUb X) h (NoUbInner L X) :=
  ⟨(noUbWg0_of_noUb L h).inner⟩

/-- The event at `w` is no undefined behaviour. -/
def NonUbAt (X : Execution) (w : EvId) : Prop := ∀ e, X.get w = some e → ∀ f, e.kind ≠ .ub f

/-- **A lane has no undefined-behaviour event before position `i`.** -/
def LaneUbFree (X : Execution) (y i : Nat) : Prop :=
  ∀ j < i, ∀ pc fl, X.get (y, j) ≠ some ⟨pc, .ub fl⟩

/-- A global absence of undefined behaviour is used where a lane's prefix is asked for. -/
instance (h : ¬ HasUb X) (y i : Nat) : CoeDep (¬ HasUb X) h (LaneUbFree X y i) :=
  ⟨fun j _ pc fl hg => h ⟨(y, j), pc, fl, hg⟩⟩

theorem LaneUbFree.of_noUbWg0 {L : Launch} {y : Nat} (h : NoUbWg0 L X)
    (hw : MbarRow.warp L y < 4) (i : Nat) :
    LaneUbFree X y i := fun j _ pc fl => h y hw j pc fl

/-- The events through an event are no undefined behaviour when it and those before it are none. -/
theorem LaneUbFree.succ {y k : Nat} {e : Event} (h : LaneUbFree X y k) (he : X.get (y, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) : LaneUbFree X y (k + 1) := fun j hj pc fl hg => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
  · exact h j h' pc fl hg
  · rw [he] at hg
    exact hub fl (by rw [Option.some.inj hg])

theorem LaneUbFree.mono {y i n : Nat} (h : LaneUbFree X y n) (hi : i ≤ n) : LaneUbFree X y i :=
  fun j hj => h j (by omega)

/-- A lane without undefined behaviour in its events before the last has none before any
position below its length. -/
theorem LaneUbFree.of_inner {L : Launch} {y : Nat} (h : NoUbInner L X)
    (hw : MbarRow.warp L y < 4) {i : Nat} (hi : i < (X.tr y).length) : LaneUbFree X y i :=
  fun j hj pc fl => h y hw j pc fl (by omega)

/-- The event of a lane of warps 0 to 3 with a successor is no undefined behaviour. -/
theorem NoUbInner.kind {L : Launch} (h : NoUbInner L X) (hw : MbarRow.warp L x < 4) {k : Nat}
    {e : Event} (he : X.get (x, k) = some e) (hs : k + 1 < (X.tr x).length) :
    ∀ f, e.kind ≠ .ub f := fun f hf =>
  h x hw k e.pc f hs (by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf])

/-- A lane without undefined behaviour in all its events has none before any position. -/
theorem LaneUbFree.all {y : Nat} (h : LaneUbFree X y (X.tr y).length) (i : Nat) :
    LaneUbFree X y i := fun j _ pc fl hg => by
  by_cases hj : j < (X.tr y).length
  · exact h j hj pc fl hg
  · have := List.getElem?_eq_none (Nat.not_lt.mp hj)
    simp only [Execution.get] at hg
    rw [this] at hg
    cases hg
/-- **An event of a lane that has a later event is no undefined behaviour.** -/
theorem noUb_kind_of_lt (hX : Consistent L kernel Assumptions.all m X) {j k : Nat} {e : Event}
    (he : X.get (x, j) = some e) (hjk : j < k) (hk : k < (X.tr x).length) :
    ∀ f, e.kind ≠ .ub f :=
  (noUbBefore_of_get hX (e := (X.tr x)[k]) (List.getElem?_eq_getElem hk)).ne hjk he

theorem LaneUbFree.ne {y i j : Nat} {e : Event} (h : LaneUbFree X y i) (hj : j < i)
    (he : X.get (y, j) = some e) : ∀ f, e.kind ≠ .ub f := NoUbBefore.ne h hj he

/-- **A lane with an exit event has no undefined behaviour**: the exit is its last event. -/
theorem LaneUbFree.of_exit {L : Launch} {y j pc : Nat}
    (hX : Consistent L kernel Assumptions.all m X) (hy : y < L.threads)
    (he : X.get (y, j) = some ⟨pc, .exit⟩) : LaneUbFree X y (X.tr y).length :=
  fun i hi pc' fl hg => by
    have hl := Execution.exit_last hX hy he
    rcases Nat.lt_or_ge i j with h | h
    · exact noUbBefore_of_get hX he i h pc' fl hg
    · obtain rfl : i = j := by omega
      rw [he] at hg
      cases hg

/-- The event of a lane of warps 0 to 3 is no undefined behaviour. -/
theorem NoUbWg0.kind {L : Launch} (h : NoUbWg0 L X) (hw : MbarRow.warp L x < 4) {k : Nat}
    {e : Event} (he : X.get (x, k) = some e) : ∀ f, e.kind ≠ .ub f := fun f hf =>
  h x hw k e.pc f (by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf])

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.Determinism

@[expose] public section

/-! # An event at a position of a lane's trace, or the lane's next event

`Occurs L X g k ev`: `ev` is the event at position `k` of lane `g`, or `k` is the end of the lane's
trace and the thread semantics fires `ev` from the lane's state there. A fact about the state
that fires an event (an event's address, its role) is proved for `Occurs`, so that it holds of the
event a pending lane is about to perform, which is in no execution yet. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

/-- The local steps of lane `g` from `t` to `t1`. -/
abbrev TauTo (L : Launch) (g : Nat) (t t1 : TState) : Prop :=
  Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1

def Occurs (L : Launch) (X : Execution) (g k : Nat) (ev : Event) : Prop :=
  X.get (g, k) = some ev ∨ (g < L.threads ∧ k = (X.tr g).length ∧ Frame.NoUbBefore X g k ∧
    ∃ t t1 mm u, Run kernel Assumptions.all L g {} (X.tr g) (some t) ∧
      TauTo L g t t1 ∧
      out kernel Assumptions.all L g t1 = .ev mm ∧ Fires t1.pc mm ev u)

variable {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {ev : Event}

theorem Occurs.lt (hX : Consistent L kernel Assumptions.all m X) (h : Occurs L X g k ev) :
    g < L.threads := by
  rcases h with h | ⟨hg, -⟩
  · exact Frame.lt_of_get hX h
  · exact hg

theorem Occurs.le (h : Occurs L X g k ev) : k ≤ (X.tr g).length := by
  rcases h with h | ⟨-, rfl, -⟩
  · exact (List.getElem?_eq_some_iff.mp h).1.le
  · exact le_rfl

theorem Occurs.noUb (hX : Consistent L kernel Assumptions.all m X) (h : Occurs L X g k ev) :
    Frame.NoUbBefore X g k := by
  rcases h with h | ⟨-, -, nu, -⟩
  · exact Frame.noUbBefore_of_get hX h
  · exact nu

end PTX.Kernels.InklingRelDecode.Proof

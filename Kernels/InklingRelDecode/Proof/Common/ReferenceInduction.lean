-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.FollowControl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Frame PTX.Flow

/-- Induction on the observed prefix of a continuously counted thread. In the
successor case the zero global fault count excludes a faulting event. -/
theorem reference_induction {Q L X g} (P : (thread Q L g).D → Prop)
    (start : P (thread Q L g).init)
    (step : ∀ {k s ev sn}, X.get (g,k)=some ev → stateAt (thread Q L) X g k=some (some s) →
      (∀ f, ev.kind≠.ub f) → P s → (thread Q L g).next s ev=some (some sn) → P sn)
    {j s} (bound : j≤(X.tr g).length) (hs : stateAt (thread Q L) X g j=some (some s))
    (clear : s.2 .ub=0) : P s := by
  induction j generalizing s with
  | zero => rw [stateAt_zero] at hs; cases hs; exact start
  | succ j ih =>
    have ev := List.getElem?_eq_getElem (l := X.tr g) (i := j) (by omega)
    rw [stateAt_succ ev] at hs
    rcases prev : stateAt (thread Q L) X g j with _|_|old <;> rw [prev] at hs <;>
      try solve | cases hs
    obtain ⟨_,cnt⟩ := Code.counted_next_some hs
    rw [cnt] at clear
    apply step ev prev _ (ih (by omega) prev (zero_before_bump clear)) hs
    intro f fault
    change _ + (if cls .ub _ then 1 else 0)=0 at clear
    simp [cls,fault] at clear

end PTX.Kernels.InklingRelDecode.Proof

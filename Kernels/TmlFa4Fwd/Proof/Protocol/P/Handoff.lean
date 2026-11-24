-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.P.Reach
public import Lemmas.Protocol.UnitHandoff
import Lemmas.Protocol.UnitItems
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The P and S-full hand-offs

* `pHandoff`: an MMA lane's poll of stage `st`'s P-full barrier with `u` earlier successful ones
  synchronizes with the arrival with `u` earlier ones of every softmax lane of the stage and every
  correction lane of the CTA.
* `p2Handoff`: its poll of the second P barrier, with the `u`-th arrival of each of the stage's four
  softmax warps.
* `sHandoff`: a softmax lane's poll of S-full with `u` earlier successful ones observes the
  notification of the commit with `u` earlier ones of the committing MMA lane. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}
  (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

omit hp hX hFw in
/-- Scopes of two threads of one CTA meet. -/
private theorem scopes {y h : Nat} (hy : y < L.threads) (hh : h < L.threads)
    (hc : y / L.block = h / L.block) : ScopesMeet L .cta y .cta h :=
  ⟨⟨hy, hh, hc⟩, hh, hy, hc.symm⟩

set_option maxRecDepth 20000 in
/-- **The P-full hand-off.** -/
theorem pHandoff (g : Nat) (st : Fin 2) :
    UnitHandoff L X (obj L g (96 + 8 * st.val))
      (fun y => ∃ a, y = pLane L (g / L.block) st.val a) (MmaIn L g) 0 := by
  refine (pObj hp hX hFw g st).handoff hX (fun _ hh => pReach hp hX hFw g st hh)
    (fun {h j pc par acq sc} hh he => ?_) (fun {a h i j pc pc' par acq sc sc'} hh ha he => ?_)
  · rcases p_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, -, -, ho, -⟩ := hk
      exact ho
    · cases hk
  · rcases p_use hp hX hFw st ha rfl (fun _ h => by cases h) with ⟨_, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩
    · cases hk
    rcases p_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨_, ⟨_, _, hk'⟩ | ⟨hk', -⟩⟩
    swap; · cases hk'
    simp only [Kind.arrive.injEq] at hk
    simp only [Kind.wait.injEq] at hk'
    obtain ⟨-, -, -, -, rfl⟩ := hk
    obtain ⟨-, -, -, -, rfl⟩ := hk'
    exact scopes (Frame.lt_of_get hX ha) hh.1
      ((pLane_facts hp (g / L.block) st.isLt a).1.trans hh.2.1.symm)

set_option maxRecDepth 20000 in
/-- **The second P hand-off.** -/
theorem p2Handoff (g : Nat) (st : Fin 2) :
    UnitHandoff L X (obj L g (112 + 8 * st.val))
      (fun y => ∃ a, y = p2Prod L X g st.val a) (MmaIn L g) 0 := by
  refine (p2Obj hp hX hFw g st).handoff hX (fun _ hh => p2Reach hp hX hFw g st hh)
    (fun {h j pc par acq sc} hh he => ?_) (fun {a h i j pc pc' par acq sc sc'} hh ha he => ?_)
  · rcases p2_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, -, -, ho, -⟩ := hk
      exact ho
    · cases hk
  · rcases p2_use hp hX hFw st ha rfl (fun _ h => by cases h) with ⟨_, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩
    · cases hk
    rcases p2_use hp hX hFw st he rfl (fun _ h => by cases h) with ⟨_, ⟨_, _, hk'⟩ | ⟨hk', -⟩⟩
    swap; · cases hk'
    simp only [Kind.arrive.injEq] at hk
    simp only [Kind.wait.injEq] at hk'
    obtain ⟨-, -, -, -, rfl⟩ := hk
    obtain ⟨-, -, -, -, rfl⟩ := hk'
    exact scopes (Frame.lt_of_get hX ha) hh.1
      ((p2Prod_spec hp st.isLt a).1.trans hh.2.1.symm)

/-- **The S-full hand-off.** -/
theorem sHandoff (g : Nat) (st : Fin 2) : ∃ c, ∀ {h j pc par u : Nat} {acq : Bool}
    {sc : MbarScope}, SoftIn L g st.val h →
      X.get (h, j) = some ⟨pc, .wait (obj L g (80 + 8 * st.val)) par true acq sc⟩ →
      okPolls (obj L g (80 + 8 * st.val)) ((X.tr h).take j) = u →
      MmaIn L g c ∧ ∃ i pc' s rank, X.get (c, i) = some ⟨pc', .tc (.commit s)⟩ ∧
        s.mbar = obj L g (80 + 8 * st.val) ∧
        ((X.tr c).take i).countP (commitsTo (obj L g (80 + 8 * st.val))) = u ∧
        rank ∈ X.tcNotified (c, i) ∧
        WaitObserves X (.async (c, i) (.tcNotify rank)) (h, j) (obj L g (80 + 8 * st.val))
          acq sc := by
  obtain ⟨c, O⟩ := sNotify hp hX hFw g st
  refine ⟨c, fun {h j pc par u acq sc} hh he hu => ?_⟩
  obtain ⟨i, pc', s, rank, hget, hb, ht, hcnt, hr, hobs⟩ :=
    O.observes hX (sReach hp hX hFw O hh) he hu
  obtain ⟨hl, hcta, hw, -, -⟩ := mma_commit_of hp hX hFw hget ht
  exact ⟨⟨hl, hcta, hw⟩, i, pc', s, rank, hget, hb, hcnt, hr, hobs⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof

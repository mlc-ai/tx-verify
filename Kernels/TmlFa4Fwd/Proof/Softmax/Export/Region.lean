-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.DataPred
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

/-- For a region of the data machine, check its entering edges once against the successor
table. A boundary event is a move from the named source, including a loop back into the region. -/
def entersOnly (region source : Site → Bool) (lz : Bool) : Bool :=
  !region .setmax && allSites.all fun s => (nexts lz s).all fun dest =>
    !(region dest) || region s || source s

/-- Induct back to the entering edge of a region. A property can refer to the actual index
and state at both ends. Staying steps (including failed polls) are part of the induction. -/
theorem soft_region_induct {p L m X g} (hp : Pre p L m) (region source : Site → Bool)
    (hc : entersOnly region source (lz L g) = true) (Q : Nat → D → Prop)
    (step : ∀ {i d d' e}, X.get (g,i) = some e → softState p L X g i = some d →
      succ p L g d e = some (some d') → region d'.site = true →
      ((region d.site = true ∧ Q i d) ∨ source d.site = true) → Q (i+1) d') :
    ∀ {i d}, i ≤ (X.tr g).length → softState p L X g i = some d → region d.site = true →
      Q i d := by
  simp only [entersOnly,Bool.and_eq_true,Bool.not_eq_true'] at hc
  intro i
  induction i with
  | zero => intro d _ hs; simp only [softState,Frame.stateAt_zero] at hs; cases hs
  | succ i ih =>
    intro d hlen hs inside
    obtain ⟨j,e,prev,eq,he,old,hn⟩ := softState_pred hp hlen hs
      (fun eq => by rw [eq,hc.1] at inside; cases inside)
    obtain rfl : j = i := by omega
    apply step he old hn inside
    by_cases src : source prev.site = true
    · exact .inr src
    · have prevIn : region prev.site = true := by
        rcases succ_cases hn with ⟨same,_⟩ | move
        · rwa [same] at inside
        · have edge := List.all_eq_true.mp (List.all_eq_true.mp hc.2 prev.site (mem_allSites _))
            d.site move.1
          simpa only [inside,Bool.not_true,Bool.false_or,Bool.or_eq_true,src,
            Bool.false_eq_true,or_false] using edge
      exact .inl ⟨prevIn,ih (by omega) old prevIn⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Values

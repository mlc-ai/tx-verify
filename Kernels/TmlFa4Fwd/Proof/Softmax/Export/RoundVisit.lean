-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundCredit
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Marker

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A closing poll has passed every marker in its round. The witness is the actual event
leaving the marker, with both its source state and its successor. -/
theorem soft_round_visit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) (a : Data.Marker) {i d}
    (hi : i ≤ (X.tr g).length) (hs : softState p L X g i = some d)
    (site : d.site = .pwend a.round) :
    ∃ j < i, ∃ e prev out, X.get (g,j) = some e ∧ softState p L X g j = some prev ∧
      prev.site = a.site ∧ succ p L g prev e = some (some out) ∧ out.site ≠ a.site ∧
      a.view prev.v = a.view d.v ∧ Tm.sPolls L X g (Prologue.warpIndex L g/4) (j+1) =
        Tm.sPolls L X g (Prologue.warpIndex L g/4) i := by
  let Q (i : Nat) (d : D) := ∃ j < i, ∃ e prev out, X.get (g,j) = some e ∧
    softState p L X g j = some prev ∧ prev.site = a.site ∧ succ p L g prev e = some (some out) ∧
    out.site ≠ a.site ∧ a.view prev.v = a.view d.v ∧
      Tm.sPolls L X g (Prologue.warpIndex L g/4) (j+1) =
        Tm.sPolls L X g (Prologue.warpIndex L g/4) i
  obtain ⟨cut,last⟩ := a.cut (lz L g)
  refine soft_region_induct hp _ _ cut Q ?_ hi hs (site.symm ▸ last)
  intro i prev out e he hprev hn inside ih
  rcases ih with ⟨pr,ih⟩ | anchor
  · obtain ⟨j,hj,ev,v,n,get,st,idx,mv,left,view,credit⟩ := ih
    exact ⟨j,by omega,ev,v,n,get,st,idx,mv,left,view.trans (a.frame hn (.inl pr) inside).symm,
      credit.trans (soft_credit_step hw he (softState_event hp hX he hprev) (a.off pr)).symm⟩
  · have site := beq_iff_eq.mp anchor
    refine ⟨i,by omega,e,prev,out,he,hprev,site,hn,?_,(a.frame hn (.inr site) inside).symm,rfl⟩
    intro eq
    simp [Data.Marker.region,eq] at inside

end PTX.Kernels.TmlFa4Fwd.Proof.Values

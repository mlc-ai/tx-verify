-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundStep
import Lemmas.Flow.GlueStep
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

/-- An interior data state comes from a specific preceding event and a successful
softmax transition, even when a different thread already stopped. -/
theorem softState_pred {p L m X g k d} (hp : Pre p L m)
    (hk : k≤(X.tr g).length) (hs : softState p L X g k = some d) (site : d.site≠.setmax) :
    ∃ i e prev, k=i+1 ∧ X.get (g,i)=some e ∧ softState p L X g i=some prev ∧
      succ p L g prev e=some (some d) := by
  cases k with
  | zero => simp only [softState,Frame.stateAt_zero] at hs; cases hs
  | succ i =>
    have hi : i < (X.tr g).length := by omega
    let e := (X.tr g)[i]
    have he : (X.tr g)[i]? = some e := List.getElem?_eq_getElem hi
    unfold softState at hs
    split at hs
    · rename_i d' n hd
      cases Option.some.inj hs
      rw [Frame.stateAt_succ he] at hd
      rcases before : Frame.stateAt (threadD p L) X g i with _ | _ | ⟨s,n0⟩ <;> rw [before] at hd
      · cases hd
      · cases hd
      obtain ⟨next,_⟩ := Code.counted_next_some (C := gluedD p L g) hd
      cases s with
      | inl s =>
        obtain ⟨z,_,h⟩ := Code.glue_inl_some next
        unfold Code.enter at h
        split at h
        · cases h
          exact (site rfl).elim
        · cases h
      | inr a =>
        obtain ⟨r,v⟩ := a
        obtain ⟨out,hn,h⟩ := Code.glue_inr_some next
        cases h
        change (SmWarp.codeT p L g).next v e = _ at hn
        rw [SmWarp.next_eq (SmWarp.numSteps hp)] at hn
        exact ⟨i,e,v,rfl,he,by simp only [softState,before],hn⟩
    · cases hs

end PTX.Kernels.TmlFa4Fwd.Proof.Values

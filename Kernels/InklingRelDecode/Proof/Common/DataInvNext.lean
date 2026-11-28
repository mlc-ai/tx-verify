-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.FollowSub
public import Kernels.InklingRelDecode.Proof.Common.DataBounds
import Kernels.InklingRelDecode.Proof.Prologue.InvNext
import Kernels.InklingRelDecode.Proof.Softmax.InvNext
import Kernels.InklingRelDecode.Proof.Epilogue.InvNext
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

private theorem soft_inv_next {ent L g s dn ev} (hi : (softCode ent L g).inv s)
    (move : (softCode ent L g).next s ev=some (some dn)) : (softCode ent L g).inv dn := by
  rcases s with d|⟨_,d⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inl_some move
    have keep := Softmax.Control.inv_next hi.1 step
    by_cases ex : sn.site=.epilogue
    · simp only [Code.enter,epiExit,ex,↓reduceIte]
      trivial
    · simp only [Code.enter,epiExit,ex,↓reduceIte]
      exact ⟨keep,by simp⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inr_some move
    exact Epilogue.Control.inv_next hi step

theorem data_inv_next {Q L m X g k w d n sn ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ev)
    (hs : stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.prologue w),d⟩,n)))
    (ok : (dataCode Q L g w).inv d) (move : (dataCode Q L g w).next d ev=some (some sn)) :
    (dataCode Q L g w).inv sn := by
  rcases d with d|⟨_,d⟩
  · obtain ⟨dn,step,rfl⟩ := Code.glue_inl_some move
    have hist := pro_known hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
    have vals := pro_known_step hp hX he hs hist step
    have payload : Prologue.Control.Payload dn := by
      constructor
      · intro h
        rw [vals.first (by omega)]
        rfl
      · intro h
        rw [vals.first (by omega),vals.last (by omega)]
        exact ⟨_,rfl⟩
    have keep := Prologue.Control.inv_next ok.1.1 step
    by_cases ex : dn.site=.exit
    · have pc : dn.site.pc=574 := ex ▸ rfl
      have words := And.intro (payload.1 (by omega)) (payload.2 (by omega))
      simp only [Code.enter,dataExit,ex,↓reduceIte]
      exact ⟨soft_initial_inv hp (lt_of_get hX he) words,rfl⟩
    · simp only [Code.enter,dataExit,ex,↓reduceIte]
      exact ⟨⟨keep,payload⟩,by simp⟩
  · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some move
    exact soft_inv_next ok step

end PTX.Kernels.InklingRelDecode.Proof

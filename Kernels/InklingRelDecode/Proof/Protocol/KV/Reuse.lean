-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Ready
public import Lemmas.Protocol.SingleTmaRing.Faults
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyPeers
import Kernels.InklingRelDecode.Proof.Mma.Export.Count

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.SingleTmaRing PTX.MbarRing

private theorem notify_item {Q L m X c s x} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hc : c<L.grid)
    (o : Notify.Obj X (Ring.empty.obj L c s) (leader L X c 7) (Ring.empty.obj L c s)
      (1-preload Q L c s))
    (hx : x ∈ Notify.S X (Ring.empty.obj L c s) (leader L X c 7) (Ring.empty.obj L c s)) :
    let S := (decl Q L X c).slot s
    x ∈ SE X S ∧ Notify.it X S.empty S.cm S.empty x.2=note X S x.1 0 x.2 := by
  let S := (decl Q L X c).slot s
  obtain ⟨⟨i,r,record,id,fault,act⟩,pc,sp,cm,obj,target,num⟩ := o.S_rec hx
  obtain ⟨_,_,warp⟩ := leader_warp (X := X) hp hc (by decide : 7<8)
  obtain ⟨_,grp,_⟩ := Mma.Export.commit hp hX hf warp cm
  change sp.mbar=S.empty at obj
  have same : TcCommit.target sp rank0=some S.empty := by
    rw [←obj]; simp [TcCommit.target,grp,rank0]
  have rk := Notify.rank_of cm same
  change Notify.rank X S.empty S.cm S.empty x.2=rank0 at rk
  have eq : Notify.it X S.empty S.cm S.empty x.2=note X S x.1 0 x.2 := by
    unfold Notify.it note
    rw [rk]
    rfl
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr ?_⟩,
    r,List.mem_of_getElem? record,id.trans eq,fault,act⟩,eq⟩
  have bounds := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
  change x.2<(X.tr S.cm).length+1 at bounds
  change x.2<useBound X S
  unfold useBound; omega

private theorem peer_guard {Q L m X g c s k pc a sp j} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (hc : c<L.grid) (hg : g<L.threads) (cta : g/L.block=c) (warp : g%L.block/32=6)
    (H : Hyp L kernel Assumptions.all X ((decl Q L X c).slot s) .cta)
    (get : X.get (leader L X c 6,k)=some ⟨pc,.tensorIssue a sp⟩)
    (obj : sp.mbar=Ring.ready.obj L c s)
    (credit : j+1≤okPolls (Ring.empty.obj L c s) ((X.tr (leader L X c 6)).take k)) :
    Relation.TransGen (DepStep L kernel X) (.thread (g,Poll.nth X (Ring.empty.obj L c s) g j),true)
      (.thread (leader L X c 6,k),false) := by
  obtain ⟨hy,cy,wy⟩ := leader_warp (X := X) hp hc (by decide : 6<8)
  have sites : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412] := by
    cases mbar_use rows hy get (l := Ring.ready.obj L c s) obj with
    | startup _ h | dispatch _ h => cases h
    | prologue h _ | softmax h _ | epilogue h _ | mma h _ => have := h.1; omega
    | loader _ h =>
      cases h with
      | readyCopy pcs _ _ _ => exact pcs
      | readyArrive _ _ _ h => cases h
      | emptyWait _ _ h => obtain ⟨_,h⟩ := h; cases h
  obtain ⟨u,len,num,path⟩ := Loader.Export.copy_peers hp hX hf wy get sites
    (hw := ⟨⟨hy,hg,cy.trans cta.symm⟩,wy.trans warp.symm⟩)
  have ag := poll_count (r := .empty) rows hg warp s u
  have ay := poll_count (r := .empty) rows hy wy s k
  rw [cta] at ag
  rw [cy] at ay
  have cr : j+1≤okPolls (Ring.empty.obj L c s) ((X.tr g).take u) := by
    change pollRound 2374 _=pollRound 2374 _ at num
    change okPolls _ _=visits _ (pollRound 2374 _) s at ag ay
    rwa [ag,num,←ay]
  exact (Relation.TransGen.single (DepStep.of_resumes L (Poll.guard H.spins len cr))).trans path

/-- Every loader lane passes its empty poll before a later reuse notification.
The first recurrent copy transfers this order across the loader warp's election. -/
theorem empty_reuse {Q L m X g c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (hc : c<L.grid) (hg : g<L.threads) (cta : g/L.block=c) (warp : g%L.block/32=6)
    (H : Hyp L kernel Assumptions.all X ((decl Q L X c).slot s) .cta)
    (fit : ((decl Q L X c).slot s).Fits)
    (o : Notify.Obj X (Ring.empty.obj L c s) (leader L X c 7) (Ring.empty.obj L c s)
      (1-preload Q L c s)) :
    let S := (decl Q L X c).slot s
    ∀ x ∈ Notify.S X S.empty S.cm S.empty, ∀ j, j+S.δ≤x.2 →
      Relation.TransGen (DepStep L kernel X) (.thread (g,Poll.nth X S.empty g j),true)
        (Notify.it X S.empty S.cm S.empty x.2,false) := by
  let S := (decl Q L X c).slot s
  dsimp only
  intro x hx j due
  obtain ⟨inS,same⟩ := notify_item hp hX hf hc o hx
  have cm := guardM H inS (Nat.le_refl x.2)
  let b : SingleTmaRing.Kind S := ⟨1,(by decide : 1<8+1)⟩
  obtain ⟨rec,obs⟩ := (ring hX H fit).observes_full (b := x.1) hX.depAcyclic
    (MbarRing.Round.Slot.present_of_guard cm) b
  obtain ⟨⟨_,r,hr,id,_,_,act⟩,_,_⟩ := SF_op H rec
  rcases item_completion H (x := (b,x.2)) (by decide : (1:Nat)≠0) (List.mem_of_getElem? hr) id
      (act (by decide : (1:Nat)≠0))
      with ⟨one,zero,_⟩|⟨_,k,pc,a,sp,which,get,obj,_,credit⟩
  · change j+S.δ≤x.2 at due
    change S.δ=1 at one
    omega
  · have prior := peer_guard hp hX hf rows hc hg cta warp H get obj
      (show j+1≤_ from (Nat.succ_le_succ (Nat.le_sub_of_add_le due)).trans credit)
    change opF X S b x.2=(S.cp,k) at which
    change Relation.TransGen (DepStep L kernel X) _ (.thread (S.cp,k),false) at prior
    rw [←which] at prior
    rw [same]
    exact (((prior.trans_left (issueF hX H rec)).tail (DepStep.of_witness L obs)).tail
      (DepStep.of_resumes L cm)).trans_left (issueE hX H inS)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV

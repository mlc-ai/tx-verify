-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarTime
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Handoff
public import Lemmas.Protocol.UnitObject
public import Lemmas.Protocol.UnitNotify
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Protocol.ObjectSource

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.MbarRow

theorem parity {Q L X o c g k pc q ok ac sc} (rows : MbarRows Q L X) (hg : g<L.threads)
    (get : X.get (g,k)=some ⟨pc,.wait (Object.loc o L c) q ok ac sc⟩) :
    q=okPolls (o.loc L c) ((X.tr g).take k)%2 := by
  obtain ⟨rfl,rfl,slot,par⟩ := wait_obj rows hg get
  rw [count rows hg o k,(Object.block_visits slot).2,par]

theorem prob_use {Q L X c s g k e} (rows : MbarRows Q L X) (hg : g<L.threads)
    (get : X.get (g,k)=some e) (hm : Frame.MbarOf e ((Object.prob s).loc L c)) :
    let l := (Object.prob s).loc L c
    e.kind=.mbInit l 1 ∨ (∃ q, Wait e l q) ∨ (g=c*L.block ∧ Arrive e l 0) := by
  obtain ⟨cta,use⟩ := uses rows hg get hm
  cases use with
  | init hk => exact .inl hk
  | probWait _ _ wait => exact .inr (.inl ⟨_,wait⟩)
  | probArrive _ zero arr =>
    have addr := Nat.div_add_mod g L.block
    rw [cta,zero,Nat.add_zero,Nat.mul_comm] at addr
    exact .inr (.inr ⟨addr.symm,arr⟩)

/-- Lane zero's probability publication is the only unit arrival on this slot. -/
theorem probability {Q L m X c} (hX : Consistent L kernel Assumptions.all m X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (s : Fin 2) :
    Unit.Obj X ((Object.prob s).loc L c) 1 (fun _ => c*L.block) 0 := by
  have ho := hX.tma.2.2.1
  let l := (Object.prob s).loc L c
  refine ⟨by decide,fun _ _ _ => Subsingleton.elim ..,?_,Mbar.initFirst hX rows init _,
    AsyncCopy.objects_noInval ho (fun _ _ ⟨_,he⟩ => Lib.no_inval hX he) _,?_,by decide⟩
  · intro r hr
    cases AsyncCopy.record_source ho hr with
    | init _ _ ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | inval _ he _ => exact (Lib.no_inval hX he).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (Lib.no_asyncArrive hX he).elim
    | bulk _ he _ _ => exact (Lib.no_copy hX he).elim
    | clc _ he _ _ _ => exact (Lib.no_clc hX he).elim
    | @tensor i _ _ _ _ he hm _ =>
      obtain ⟨g,k⟩ := i
      rcases prob_use rows (Frame.lt_of_get hX he) he hm with kd|⟨_,_,kd⟩|⟨_,kd⟩ <;> cases kd
    | @commit i _ _ rank _ he ht _ =>
      obtain ⟨g,k⟩ := i
      rcases prob_use rows (Frame.lt_of_get hX he) he ⟨rank,ht⟩ with kd|⟨_,_,kd⟩|⟨_,kd⟩ <;>
        cases kd
    | arrive hid he ha =>
      rcases prob_use rows (Frame.lt_of_get hX he) he rfl with kd|⟨_,_,kd⟩|⟨owner,kd⟩
      · cases kd
      · cases kd
      · obtain ⟨_,rfl,rfl,rfl,rfl⟩ := Kind.arrive.inj kd
        exact .arrive hid ⟨0,owner⟩ he ha
  · intro g k pc q ac sc get
    rw [parity rows (Frame.lt_of_get hX get) get]
    simp

private theorem notify_use {Q L X c o g k e} (rows : MbarRows Q L X) (hg : g<L.threads)
    (get : X.get (g,k)=some e) (hm : Frame.MbarOf e (Object.loc o L c))
    (cm : (∃ s,o=.score s) ∨ o=.done) :
    let l := o.loc L c
    e.kind=.mbInit l 1 ∨ (∃ q, Wait e l q) ∨
      (g/L.block=c ∧ g%L.block/32=7 ∧ e.pc ∈ [2499,2548] ∧ Commit e l) := by
  obtain ⟨cta,use⟩ := uses rows hg get hm
  cases use with
  | init hk => exact .inl hk
  | scoreWait _ _ wait | doneWait _ _ wait => exact .inr (.inl ⟨_,wait⟩)
  | scoreCommit pc warp kd | doneCommit pc warp kd => exact .inr (.inr ⟨cta,warp,by simp [pc],kd⟩)
  | probArrive | probWait => rcases cm with ⟨s,h⟩|h <;> cases h

/-- Score and output-done updates are elected, single-CTA commit notifications. -/
theorem notification {Q L m X c o} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (cm : (∃ s,o=.score s) ∨ o=.done) :
    Notify.Obj X (Object.loc o L c) (KV.leader L X c 7) (o.loc L c) 0 := by
  refine Notify.Obj.of_commits hX (Mbar.initFirst hX rows init _) ?_ ?_
    (fun he _ => Lib.no_copy hX he) (fun he _ => Lib.no_asyncArrive hX he)
    (Lib.no_clc hX) (Lib.no_inval hX) ?_ ?_ (by decide)
  · intro g k pc tx n rel sc get
    rcases notify_use rows (Frame.lt_of_get hX get) get rfl cm with kd|⟨_,_,kd⟩|⟨_,_,_,_,kd,_⟩ <;>
      cases kd
  · rintro ⟨g,k⟩ pc a sp get obj
    rcases notify_use rows (Frame.lt_of_get hX get) get obj cm with kd|⟨_,_,kd⟩|⟨_,_,_,_,kd,_⟩ <;>
      cases kd
  · rintro ⟨g,k⟩ pc sp rank get ht
    have hg := Frame.lt_of_get hX get
    rcases notify_use rows hg get ⟨rank,ht⟩ cm with kd|⟨_,_,kd⟩|⟨cta,warp,site,sp',kd,addr,_⟩
    · cases kd
    · cases kd
    obtain rfl := TcKind.commit.inj (Kind.tc.inj kd)
    obtain ⟨ev,mem,won⟩ := Mma.Export.elected hp hX hf get (fun _ => nofun)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at site ⊢; tauto)
    have lead := KV.leader_eq hX hg ⟨ev,(List.take_sublist k _).subset mem,won⟩
    rw [cta,warp] at lead
    exact ⟨lead.symm,addr⟩
  · intro g k pc q ac sc get
    rw [parity rows (Frame.lt_of_get hX get) get]
    simp

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Handoff
import Kernels.InklingRelDecode.Proof.Epilogue.Export.FinalCount
import Kernels.InklingRelDecode.Proof.Mma.Export.FinalCount
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.NotifyBlocker
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal
open PTX PTX.Flow MbarRow PTX.MbarRow

def obj (L : Launch) (c : Nat) : Loc := ⟨.shared,c,L.sharedBase+Iface.oFinal⟩

private theorem other {L c g n} (lt : n<Iface.oFinal) (eq : obj L c=loc L g n) : False := by
  have off := (Loc.mk.inj eq).2.2
  exact lt.ne (Nat.add_left_cancel off).symm

theorem use {Q L X c g k e} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some e) (hm : Frame.MbarOf e (obj L c)) :
    e.kind=.mbInit (obj L c) 1 ∨
      (e.pc=2565 ∧ Wait e (obj L c) 0) ∨
      (e.pc=2553 ∧ g/L.block=c ∧ g%L.block/32=7 ∧ Commit e (obj L c)) := by
  have ready : ∀ s, Iface.kvReady s<Iface.oFinal := by decide
  have empty : ∀ s, Iface.kvEmpty s<Iface.oFinal := by decide
  have score : ∀ s, Iface.sReady s<Iface.oFinal := by decide
  have prob : ∀ s, Iface.pReady s<Iface.oFinal := by decide
  cases mbar_use rows hg he hm with
  | dispatch _ h | startup _ h => cases h
  | prologue _ h =>
    cases h with
    | init _ _ _ hk _ _ _ _ _ => exact .inl hk
    | preloadArrive _ _ addr _ | preloadCopy _ _ addr _ => exact (other (ready _) addr).elim
  | loader _ h =>
    cases h with
    | emptyWait _ addr _ => exact (other (empty _) addr).elim
    | readyArrive _ _ addr _ | readyCopy _ _ addr _ => exact (other (ready _) addr).elim
  | epilogue _ h => cases h with | finalWait pc _ wait => exact .inr (.inl ⟨pc,wait⟩)
  | softmax _ h =>
    cases h with
    | sWait _ addr _ => exact (other (score _) addr).elim
    | pArrive _ _ addr _ => exact (other (prob _) addr).elim
    | oWait _ addr _ => exact (other (by decide : Iface.oDone<Iface.oFinal) addr).elim
  | mma hw h =>
    cases h with
    | readyWait _ addr _ => exact (other (ready _) addr).elim
    | pWait _ addr _ => exact (other (prob _) addr).elim
    | sCommit _ addr _ => exact (other (score _) addr).elim
    | emptyCommit _ addr _ => exact (other (empty _) addr).elim
    | doneCommit _ addr _ => exact (other (by decide : Iface.oDone<Iface.oFinal) addr).elim
    | finalCommit pc addr kind => exact .inr (.inr ⟨pc,(Loc.mk.inj addr).2.1.symm,hw.1,kind⟩)

theorem wait_info {Q L X c g k pc p ok ac sc} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨pc,.wait (obj L c) p ok ac sc⟩) : pc=2565 ∧ p=0 := by
  rcases use rows hg he rfl with bad|⟨pc,_,kind⟩|⟨_,_,_,_,bad,_⟩
  · cases bad
  · exact ⟨pc,(Kind.wait.inj kind).2.1⟩
  · cases bad

theorem wait_first {Q L m X c g k pc p ok ac sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (he : X.get (g,k)=some ⟨pc,.wait (obj L c) p ok ac sc⟩) :
    okPolls (obj L c) ((X.tr g).take k)=0 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨rfl,_⟩ := wait_info rows hg he
  have first := Epilogue.Export.final_first hp hX hf (fun h => Shared.role_bytes hp hX h) he
  by_contra! pos
  obtain ⟨j,pc,_,_,_,jk,get⟩ := exists_okPoll (by omega : 0<okPolls (obj L c) ((X.tr g).take k))
  obtain ⟨rfl,_⟩ := wait_info rows hg get
  have mem := List.mem_iff_getElem?.mpr ⟨j,(List.getElem?_take_of_lt jk).trans get⟩
  exact List.countP_eq_zero.mp first _ mem rfl

theorem commit_info {Q L X c g k pc sp rank} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨pc,.tc (.commit sp)⟩) (ht : TcCommit.target sp rank=some (obj L c)) :
    pc=2553 ∧ g/L.block=c ∧ g%L.block/32=7 ∧ sp.mbar=obj L c := by
  rcases use rows hg he ⟨rank,ht⟩ with bad|⟨_,_,bad⟩|⟨pos,cta,warp,_,kind,addr,_⟩
  · cases bad
  · cases bad
  · obtain rfl := TcKind.commit.inj (Kind.tc.inj kind)
    exact ⟨pos,cta,warp,addr⟩

theorem history {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X) :
    MbarRing.Notify.Obj X (obj L c) (KV.leader L X c 7) (obj L c) 0 := by
  refine MbarRing.Notify.Obj.of_commits hX (Mbar.initFirst hX rows init _) ?_ ?_
    (fun he _ => Lib.no_copy hX he) (fun he _ => Lib.no_asyncArrive hX he)
    (Lib.no_clc hX) (Lib.no_inval hX) ?_ ?_ (by decide)
  · intro g k pc tx cnt rel sc he
    rcases use rows (Frame.lt_of_get hX he) he rfl with bad|⟨_,_,bad⟩|⟨_,_,_,_,bad,_⟩
    all_goals cases bad
  · rintro ⟨g,k⟩ pc a sp he hm
    rcases use rows (Frame.lt_of_get hX he) he hm with bad|⟨_,_,bad⟩|⟨_,_,_,_,bad,_⟩
    all_goals cases bad
  · rintro ⟨g,k⟩ pc sp rank he ht
    have hg := Frame.lt_of_get hX he
    obtain ⟨rfl,cta,warp,addr⟩ := commit_info rows hg he ht
    obtain ⟨ev,mem,won⟩ := Mma.Export.elected hp hX hf he (fun _ => nofun)
      (by change 2553 ∈ _; decide)
    have lead := KV.leader_eq hX hg ⟨ev,(List.take_sublist k _).subset mem,won⟩
    rw [cta,warp] at lead
    exact ⟨lead.symm,addr⟩
  · intro g k pc p ac sc he
    rw [(wait_info rows (Frame.lt_of_get hX he) he).2,wait_first hp hX hf rows he]

theorem target_zero {Q L m X g i pc sp l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,i)=some ⟨pc,.tc (.commit sp)⟩) (addr : sp.mbar=l) :
    TcCommit.target sp 0=some l := by
  have warp := Mma.Export.commit_warp hp hX hf get
  obtain ⟨off,rfl,_⟩ := Mma.Export.commit hp hX hf warp get
  rw [←addr]
  simp [TcCommit.target]

theorem commit_zero {Q L m X g i pc sp c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (he : X.get (g,i)=some ⟨pc,.tc (.commit sp)⟩) (objEq : sp.mbar=obj L c) :
    ((X.tr g).take i).countP (commitsTo (obj L c))=0 := by
  obtain ⟨rfl,_,_,_⟩ := commit_info rows (Frame.lt_of_get hX he) he (target_zero hp hX hf he objEq)
  have fresh := Mma.Export.final_first hp hX hf (fun h => Shared.role_bytes hp hX h) he
  by_contra! nz
  have prior : 0<((X.tr g).take i).countP (commitsTo (obj L c)) := by omega
  obtain ⟨ev,mem,counted⟩ := List.countP_pos_iff.mp prior
  obtain ⟨j,get⟩ := List.mem_iff_getElem?.mp mem
  have lt := (List.getElem?_eq_some_iff.mp get).1
  rw [List.length_take] at lt
  have ji : j < i := by omega
  rw [List.getElem?_take_of_lt ji] at get
  obtain ⟨prev,kind,addr⟩ := MbarRing.Notify.commit_of_commitsTo counted
  obtain ⟨p,kd⟩ := ev
  cases kind
  obtain ⟨rfl,_,_,_⟩ := commit_info rows (Frame.lt_of_get hX get) get
    (target_zero hp hX hf get addr)
  exact fresh j ji _ get

theorem fault_free {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X) :
    ∀ r ∈ X.objects (obj L c), r.fault=none := by
  apply MbarRing.Notify.Obj.fault_free hX (history hp hX hf rows init)
  apply MbarRing.Notify.gated_of_paths
  intro i pc sp rank he addr _ _ prior
  have zero := commit_zero hp hX hf rows he addr
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal

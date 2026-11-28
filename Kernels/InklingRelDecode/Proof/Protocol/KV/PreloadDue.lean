-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.LoaderDue
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
import Kernels.InklingRelDecode.Proof.Prologue.Export.Packet
import Kernels.InklingRelDecode.Proof.Protocol.Warp.Leader

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched PTX.MbarRing

private theorem published {Q L m X g y c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hw : Waiting L m X .ready c s g)
    (cta : y/L.block=c) (low : y%L.block<128) :
    ∃ k, X.get (y,k)=some ⟨573,.bar 1 none .sync⟩ := by
  obtain ⟨rfl,_,_,⟨Y,hY,pref,get⟩⟩ := hw
  have phase := Export.after_initialization hp hY get (by simp)
    (by decide : Export.afterInit 2462=true)
  rw [pref] at phase
  obtain ⟨k,ev,_⟩ := Mbar.data_published hp hX phase cta low
  exact ⟨k,ev⟩

theorem preload_arrive_due {Q L m X g c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hw : Waiting L m X .ready c s g) :
    let l := Ring.ready.obj L c s
    Due Q L X g (arrivalLane L c 0) (arrivesOn l)
      (dueArr (preload Q L c s) (okPolls l (X.tr g)+1) 0) := by
  let y := arrivalLane L c 0
  have cta : y/L.block=c := by simp [y,arrivalLane,hp.block]
  have tid : y%L.block=0 := by simp [y,arrivalLane,hp.block]
  by_cases active : s.val<Iface.preloadCount Q L c
  · obtain ⟨k,get⟩ := published hp hX hw cta (by omega)
    obtain ⟨j,e,seen,kd⟩ := Prologue.Export.preload_arrived hp hX hf get (by rw [tid])
      s (by rwa [cta])
    rw [cta] at kd
    have pos : 0<(X.tr y).countP (arrivesOn (Ring.ready.obj L c s)) :=
      List.countP_pos_iff.mpr ⟨e,List.mem_of_getElem? seen,by
        cases e with | mk pc val => cases kd; simp [arrivesOn,sourceArrive,Iface.kvReadyLoc,
          Ring.obj,Ring.offset]⟩
    have full := Nat.succ_le_of_lt pos
    simpa [Due,dueArr,preload,active,y] using
      (show (∀ k pc, X.get (y,k)=some ⟨pc,.exit⟩ → 1≤_) ∧ (_ → 1≤_)
        from ⟨fun _ _ _ => full,fun _ => full⟩)
  · simp [Due,dueArr,preload,active]

theorem preload_copy_due {Q L m X g c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hw : Waiting L m X .ready c s g) (b : Fin 3) (pro : b≠2) :
    let l := Ring.ready.obj L c s
    Due Q L X g (copyLane L X c b) (issuesTo l)
      (dueCp (preload Q L c s) (okPolls l (X.tr g)+1) b) := by
  have hg := hw.2.choose_spec.choose_spec.lt
  have cEq := hw.1
  have hc : c<L.grid := by
    rw [←cEq]; exact Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  let y := leader L X c b.val
  have warp : b.val<2 := by omega
  obtain ⟨_,cta,geo⟩ := leader_warp (X := X) hp hc (show b.val<8 by omega)
  have low : y%L.block<64 := by change y%L.block/32=b.val at geo; omega
  by_cases active : s.val<Iface.preloadCount Q L c
  · obtain ⟨k,get⟩ := published hp hX hw cta (by omega)
    have full : 4≤(X.tr y).countP (issuesTo (Ring.ready.obj L c s)) := by
      apply Lib.count_of_occurrences (fun _ e => (MbarRow.preloadCopies s).idxOf e.pc)
      intro i
      obtain ⟨j,e,seen,pc,_,sp,kd,bar,_⟩ := Prologue.Export.preload_copied hp hX hf get
        (by omega) (Warp.leader_wins hp hX hc (by omega)) s (by rwa [cta]) i
      rw [cta] at bar
      refine ⟨j,e,seen,by simp [issuesTo,kd,bar,Iface.kvReadyLoc,Ring.obj,Ring.offset],?_⟩
      rw [pc]
      exact (by decide : ∀ s (i : Fin 4), (MbarRow.preloadCopies s).idxOf
        ((MbarRow.preloadCopies s).getD i 0)=i.val) s i
    simpa [Due,dueCp,preload,active,copyLane,pro,y] using
      (show (∀ k pc, X.get (y,k)=some ⟨pc,.exit⟩ → 4≤_) ∧ (_ → 4≤_)
        from ⟨fun _ _ _ => full,fun _ => full⟩)
  · simp [Due,dueCp,preload,active,pro]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV

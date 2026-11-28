-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
public import Lemmas.Flow.ElectLead
import Kernels.InklingRelDecode.Proof.Common.FollowSub
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Prologue.PacketCrossing
import Kernels.InklingRelDecode.Proof.Prologue.ShapeCopy
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.Final
import Lemmas.Flow.TensorIssue

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Frame Control

private theorem crossed {Q L m X g w k d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (b : Fin 3) (op : Option (Fin 4)) (active : b.val<Iface.preloadCount Q L (g/L.block))
    (arr : op=none → g%L.block%128=0)
    (copy : op.isSome → g%L.block%128<64 ∧ ElectLead L g (X.tr g))
    (len : k≤(X.tr g).length) (state : stateAt (thread Q L) X g k=some (some (proState w d n)))
    (later : (packetSite b op).pc<d.site.pc) :
    ∃ u s cnt, u<k ∧ stateAt (thread Q L) X g u=some (some (proState w s cnt)) ∧
      s.site=packetSite b op := by
  induction k using Nat.strong_induction_on generalizing d n with
  | h k ih =>
    have ne : d≠{} := by rintro rfl; exact (by decide : ∀ b op, ¬(packetSite b op).pc<27) b op later
    obtain ⟨u,old,cnt,ev,eq,prev,get,step⟩ := pro_prev len ne state
    by_cases lo : old.site.pc≤(packetSite b op).pc
    · obtain ⟨_,hist⟩ := (reached_table hf hg (noUbBefore_of_get hX get) prev).2
      apply Exists.intro u
      refine ⟨old,cnt,by omega,prev,packet_cross step b op ?_ arr ?_ lo later⟩
      · intro l
        have e := preload_count hp hg (hist.known.first (by omega)) (hist.known.last (by omega))
          (hist.known.seq l)
        rw [←e] at active
        omega
      · intro someOp
        obtain ⟨tid,wins⟩ := copy someOp
        exact ⟨tid,wins _ (List.mem_of_getElem? get)⟩
    · obtain ⟨v,s,c,hv,hs,site⟩ := ih u (by omega)
        (by omega) prev (by omega)
      exact ⟨v,s,c,by omega,hs,site⟩

private theorem seen {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (sync : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩)
    (b : Fin 3) (op : Option (Fin 4)) (active : b.val<Iface.preloadCount Q L (g/L.block))
    (arr : op=none → g%L.block%128=0)
    (copy : op.isSome → g%L.block%128<64 ∧ ElectLead L g (X.tr g)) :
    ∃ j e w d t ins o, X.get (g,j)=some e ∧ d.site=packetSite b op ∧
      (code Q L g w).AtD d t ∧ kernel.code[d.site.pc]?=some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o ∧ e.pc=d.site.pc ∧
      (∀ f, e.kind≠.ub f) := by
  have hg := lt_of_get hX sync
  obtain ⟨st,hs,_⟩ := good_stateU (fun g h => thread_sound hp h) hX sync
    (by simp) (hf g hg k)
  have pc := event_pcU (fun g h => thread_sound hp h) hX sync hs (by simp)
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role st).prologue (by decide) (by decide)
  have len := (List.getElem?_eq_some_iff.mp sync).1
  change k<(X.tr g).length at len
  change 573=d.site.pc at pc
  obtain ⟨u,s,c,uk,prev,site⟩ := crossed hp hX hf hg
    b op active arr copy len.le hs (pc ▸ (by decide : ∀ b op, (packetSite b op).pc<573) b op)
  have get := List.getElem?_eq_getElem (l := X.tr g) (i := u) (by omega)
  have clean := noUbBefore_of_get hX sync u uk _ get
  obtain ⟨t,ins,o,hat,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX get prev clean
  exact ⟨_,_,_,_,_,_,_,get,site,hat,hc,fire,
    event_pcU (fun g h => thread_sound hp h) hX get prev clean,clean⟩

public theorem preload_arrived {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (sync : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩) (lane : g%L.block%128=0)
    (b : Fin 3) (active : b.val<Iface.preloadCount Q L (g/L.block)) :
    ∃ j e, X.get (g,j)=some e ∧
      e.kind=.arrive (Iface.kvReadyLoc L (g/L.block) b) 65536 1 true .cta := by
  obtain ⟨_,_,_,_,_,_,_,get,site,hat,hc,fire,_,_⟩ :=
    seen hp hX hf sync b none active (fun _ => lane) (by simp)
  exact ⟨_,_,get,arrive_shape hp hat b site hc fire⟩

public theorem preload_copied {Q L m X g k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (sync : X.get (g,k)=some ⟨573,.bar 1 none .sync⟩) (tid : g%L.block%128<64)
    (wins : ElectLead L g (X.tr g)) (b : Fin 3) (active : b.val<Iface.preloadCount Q L (g/L.block))
    (i : Fin 4) : ∃ j e, X.get (g,j)=some e ∧ e.pc=(MbarRow.preloadCopies b).getD i 0 ∧
      PTX.MbarRow.Issue e (Iface.kvReadyLoc L (g/L.block) b) 8192 := by
  obtain ⟨j,e,w,d,t,ins,o,get,site,hat,hc,fire,pc,nu⟩ :=
    seen hp hX hf sync b (some i) active (by simp) (fun _ => ⟨tid,wins⟩)
  have hc' := hc
  obtain ⟨guard,dst,cs,fetch⟩ := copy_instr b i
  rw [site] at hc'
  obtain rfl := Option.some.inj (hc'.symm.trans fetch)
  have live : ∃ v, o=some v := by
    cases o with
    | some _ => exact ⟨_,rfl⟩
    | none =>
      rcases fires_none_ends fire with ⟨f,ub⟩|ex
      · exact (nu f ub).elim
      · have ret := Lib.ret_pc' hc fire ex
        rw [site] at ret
        exact (by decide : ∀ b i, (packetSite b (some i)).pc ∉ Lib.retPcs) b i ret |>.elim
  obtain ⟨_,rfl⟩ := live
  obtain ⟨_,sp,ev,_,_⟩ := fires_cpTensor_issue fire
  refine ⟨_,_,get,pc.trans ?_,copy_shape hp hat b i site hc fire (congrArg Event.kind ev)⟩
  rw [site]
  exact (by decide : ∀ b i, (packetSite b (some i)).pc=(MbarRow.preloadCopies b).getD i 0) b i

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

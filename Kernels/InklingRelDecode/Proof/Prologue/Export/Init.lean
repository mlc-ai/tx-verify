-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
public import Lemmas.Flow.ElectLead
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Common.FollowSub
import Kernels.InklingRelDecode.Proof.Prologue.InitCrossing
import Kernels.InklingRelDecode.Proof.Prologue.Shape
import Lemmas.Kernel.Safety.TableU

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Frame Control

private theorem crossed {Q L X g w k d n} (j : Fin 12) (warp : g%L.block<32)
    (wins : ElectLead L g (X.tr g)) (bound : k≤(X.tr g).length)
    (state : stateAt (thread Q L) X g k=some (some (proState w d n))) (later : initPc j<d.site.pc) :
    ∃ u s cnt, u<k ∧ stateAt (thread Q L) X g u=some (some (proState w s cnt)) ∧
      s.site=.init j := by
  induction k using Nat.strong_induction_on generalizing d n with
  | h k ih =>
    have ne : d≠{} := by
      rintro rfl
      exact (by decide : ∀ j : Fin 12, ¬initPc j<27) j later
    obtain ⟨u,old,cnt,ev,eq,prev,get,step⟩ := pro_prev bound ne state
    by_cases lo : old.site.pc ≤ initPc j
    · exact ⟨_,_,_,by omega,prev,crosses_init step (wins ev (List.mem_of_getElem? get))
        warp j lo later⟩
    · obtain ⟨v,s,c,hv,hs,site⟩ := ih u (by omega) (by omega) prev (by omega)
      exact ⟨v,s,c,by omega,hs,site⟩

/-- Each initializer has already fired when the elected warp-zero lane reaches a
nonfaulting event at or after the Prologue's publishing barrier at 180. -/
public theorem initialized {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ev)
    (nu : ∀ f, ev.kind≠.ub f) (lo : 180≤ev.pc) (hi : ev.pc<574)
    (warp : g%L.block<32) (wins : ElectLead L g (X.tr g)) (j : Fin 12) :
    ∃ u<k, X.get (g,u)=some ⟨134+4*j.val,.mbInit (MbarRow.loc L g (MbarRow.initOffset j)) 1⟩ := by
  have hg := lt_of_get hX he
  obtain ⟨st,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => nu f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role st).prologue (by omega) hi
  have len := (List.getElem?_eq_some_iff.mp he).1
  change k<(X.tr g).length at len
  change ev.pc=d.site.pc at pc
  have bound := (by decide : ∀ j : Fin 12, initPc j<180) j
  obtain ⟨u,s,c,uk,prev,init⟩ := crossed j warp wins len.le hs (by omega)
  have get := List.getElem?_eq_getElem (l := X.tr g) (i := u) (by omega)
  have clean := noUbBefore_of_get hX he u uk _ get
  obtain ⟨t,ins,o,hat,_,code,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg)
    hX get prev clean
  have kind := init_shape hp hat j init code fire
  have pos := event_pcU (fun g hg => thread_sound hp hg) hX get prev clean
  change (X.tr g)[u].pc=s.site.pc at pos
  rw [init] at pos
  have eq : (X.tr g)[u]=⟨134+4*j.val,.mbInit (MbarRow.loc L g (MbarRow.initOffset j)) 1⟩ :=
    by generalize (X.tr g)[u]=v at pos kind ⊢; cases v; congr 1
  exact ⟨u,uk,get.trans (congrArg some eq)⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

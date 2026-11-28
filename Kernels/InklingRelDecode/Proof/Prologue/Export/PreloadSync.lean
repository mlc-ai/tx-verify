-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Common.FollowSub
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
import Kernels.InklingRelDecode.Proof.Prologue.BarrierCrossing
import Kernels.InklingRelDecode.Proof.Prologue.FenceCrossing
import Kernels.InklingRelDecode.Flow.Code.Part002
import Lemmas.Flow.TmemOperands
import Lemmas.Flow.RoleTemplates
import Lemmas.Flow.NthEv
import Lemmas.Kernel.Safety.TableU

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Frame Control

private theorem crossed {Q L X g w k d n} (bound : k≤(X.tr g).length)
    (state : stateAt (thread Q L) X g k=some (some (proState w d n))) (later : 180<d.site.pc) :
    ∃ u s cnt, u<k ∧ stateAt (thread Q L) X g u=some (some (proState w s cnt)) ∧
      s.site=.bar2 := by
  induction k using Nat.strong_induction_on generalizing d n with
  | h k ih =>
    have ne : d≠{} := by rintro rfl; exact (by decide : ¬180<27) later
    obtain ⟨u,old,cnt,ev,eq,prev,get,step⟩ := pro_prev bound ne state
    by_cases lo : old.site.pc≤180
    · exact ⟨_,_,_,by omega,prev,crosses_barrier step lo later⟩
    · obtain ⟨v,s,c,hv,hs,site⟩ := ih u (by omega) (by omega) prev (by omega)
      exact ⟨v,s,c,by omega,hs,site⟩

public theorem preload_phase {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some e)
    (nu : ∀ f, e.kind≠.ub f) (lo : 180<e.pc) (hi : e.pc<574) :
    3≤((X.tr g).take k).countP (Execution.isBarId 0) := by
  have hg := lt_of_get hX he
  obtain ⟨st,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => nu f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role st).prologue (by omega) hi
  have len : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  change e.pc=d.site.pc at pc
  obtain ⟨u,s,c,uk,prev,site⟩ := crossed len.le hs (by omega)
  have get := List.getElem?_eq_getElem (l := X.tr g) (i := u) (by omega)
  have clean := noUbBefore_of_get hX he u uk _ get
  obtain ⟨t,ins,o,_,_,code,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX get prev clean
  change kernel.code[s.site.pc]?=some ins at code
  rw [site] at code
  obtain rfl := Option.some.inj (Flow.code_180.symm.trans code)
  have kind := fires_barSyncN_imm (id := 0) (n := 128) (by decide) (by decide) (by decide)
    (by decide) (by rw [hp.block]; decide) fire
  have before : 2≤c0 X g u := by
    by_contra! lt
    obtain ⟨_,_,earlyState,_⟩ := early_at hp hX get (fun f bad => clean f (by
      generalize hh : (X.tr g)[u]=v at bad ⊢; cases v; cases bad; rfl)) (by omega)
    rw [prev] at earlyState
    cases earlyState
  have mono := countP_take_mono (Execution.isBarId 0) (X.tr g) uk
  rw [List.take_add_one,get,kind,List.countP_append] at mono
  change c0 X g u+1≤_ at mono
  omega

/-- **A lane that issues a preload copy has made its shared proxy fence before**: the fence at
the prologue's pc 179, directly before the lane's first rendezvous of the data warps. -/
public theorem preload_fence {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some e)
    (nu : ∀ f, e.kind≠.ub f) (lo : 180<e.pc) (hi : e.pc<574) :
    ∃ uf, uf<k ∧ X.get (g,uf)=some ⟨179,.fenceProxy (.async (some (.shared .cta))) none⟩ := by
  have hg := lt_of_get hX he
  obtain ⟨st,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => nu f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role st).prologue (by omega) hi
  have len : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  change e.pc=d.site.pc at pc
  obtain ⟨u,s,c,uk,prev,site⟩ := crossed len.le hs (by omega)
  have later : s≠{} := by
    rintro rfl
    cases site
  obtain ⟨uf,old,cnt,ev,eq,prevf,getf,step⟩ := pro_prev (by omega) later prev
  have fnc : old.site=.fnc0 := barrier_predecessor step site
  have clear := noUbBefore_of_get hX he uf (by omega) _ getf
  obtain ⟨t,ins,o,_,_,code,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX getf prevf clear
  change kernel.code[old.site.pc]?=some ins at code
  rw [fnc] at code
  obtain rfl := Option.some.inj (Flow.code_179.symm.trans code)
  obtain ⟨shape,_⟩ := fires_fence_proxy fire
  refine ⟨uf,by omega,?_⟩
  have at179 : (thread Q L g).pc (proState w old cnt) = 179 := by
    change old.site.pc = 179
    rw [fnc]
    rfl
  rw [getf,shape,at179]
  rfl

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

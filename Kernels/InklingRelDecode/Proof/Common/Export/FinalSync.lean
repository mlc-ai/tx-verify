-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.BarOne
public import Kernels.InklingRelDecode.Spec
import Kernels.InklingRelDecode.Proof.Common.FinalPrefix
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Kernel.Safety.Handoff
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Proof PTX.Flow PTX.Frame
variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem visits {g k e} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some e) (hu : ∀ f, e.kind≠.ub f) :
    ((X.tr g).take k).countP (fun ev => Lib.finalSync ev.pc) = Lib.afterFinal e.pc := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f eq => hu f (congrArg Event.kind eq))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  rw [Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs hu]
  exact final_prefix hp hX hg (Frame.noUbBefore_of_get hX he) hs

theorem final_late {g j pc} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,j)=some ⟨pc,.bar 0 none .sync⟩) :
    Lib.finalSync pc=true ↔ 2≤((X.tr g).take j).countP (Execution.isBarId 0) := by
  change Lib.finalSync pc=true ↔ 2≤c0 X g j
  obtain ⟨_,bad|full|half⟩ := Lib.recorded_bar hX hp.block he
  · cases bad.1
  · have hg := Frame.lt_of_get hX he
    rcases early hp hX j (noUb_before hX he) with miss|⟨dead,_⟩|⟨s,hs,pos⟩
    · obtain ⟨_,live,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
        hX he (by simp) ⟨control_tracked hp hX g j hg,fun _ _ => trivial⟩
      rw [miss] at live; cases live
    · obtain ⟨_,live,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
        hX he (by simp) ⟨control_tracked hp hX g j hg,fun _ _ => trivial⟩
      rw [dead] at live; cases live
    have cnt : s.2 (.bar 0)=c0 X g j := by rw [fcount hs,cls_bar0]
    have p := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    change pc=_ at p
    have pcs := full.2.2
    simp only [BarRow.fullZeroSites,List.mem_cons,List.not_mem_nil,or_false] at pcs
    rcases pcs with rfl|rfl|rfl|rfl
    all_goals first
      | (obtain ⟨⟨site,t,x,w⟩,n,rfl⟩ := (p ▸ state_role s).startup (by decide)
         change _=site.pc at p
         cases site <;> first | contradiction | (rename_i r; cases r <;> contradiction) |
           (simp only [EarlyPos] at pos; change n (.bar 0)=_ at cnt; simp [Lib.finalSync]; omega))
      | (change true=true ↔ _; simp only [true_iff]; rcases s with ⟨s,n⟩
         rcases s with ⟨site,t,x,w⟩|r
         · change _=site.pc at p
           cases site <;> first | contradiction | (rename_i r; cases r <;> contradiction)
         · exact cnt ▸ pos)
  · have := half.2.1
    rw [hp.block] at this
    cases this

/-- A final rendezvous is the first of its lane. -/
theorem final_first {g j pc} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,j)=some ⟨pc,.bar 0 none .sync⟩) (site : Lib.finalSync pc=true) :
    ((X.tr g).take j).countP (fun ev => Lib.finalSync ev.pc)=0 := by
  rw [visits hp hX he (by simp)]
  simp only [Lib.finalSync,Bool.or_eq_true,beq_iff_eq] at site
  rcases site with rfl|rfl <;> rfl

/-- An event after the final rendezvous follows a final `bar.sync 0` of its lane, after both
startup arrivals. -/
theorem final_bar_before {g j e} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,j)=some e) (nu : ∀ f, e.kind≠.ub f) (late : Lib.afterFinal e.pc=1) :
    ∃ u p, u<j ∧ X.get (g,u)=some ⟨p,.bar 0 none .sync⟩ ∧ Lib.finalSync p=true ∧
      2≤((X.tr g).take u).countP (Execution.isBarId 0) := by
  have cnt := visits hp hX he nu
  rw [late] at cnt
  obtain ⟨u,ev,get,hit,_⟩ := MbarRing.Slot.exists_nth_countP
    (fun e : Event => Lib.finalSync e.pc) (c := 0) cnt.ge
  have uj : u<j := by
    have ub := (List.getElem?_eq_some_iff.mp get).1
    rw [List.length_take] at ub
    omega
  rw [List.getElem?_take_of_lt uj] at get
  have kind := Lib.final_kind hX (i := (g,u)) get hit (Frame.noUbBefore_of_get hX he u uj ev get)
  rcases ev with ⟨p,kd⟩
  cases kind
  exact ⟨u,p,uj,get,hit,(final_late hp hX get).mp hit⟩

/-- An exit is preceded by a full barrier-0 event after both startup arrivals. -/
theorem exit_final_bar {g j pc} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,j)=some ⟨pc,.exit⟩) :
    ∃ u p, u<j ∧ X.get (g,u)=some ⟨p,.bar 0 none .sync⟩ ∧
      2≤((X.tr g).take u).countP (Execution.isBarId 0) := by
  have cnt := visits hp hX he (by simp)
  obtain ⟨_,bad⟩|⟨_,_,_,_,hc,fire⟩ := get_source hX he
  · cases bad
  have ret := Lib.ret_pc' hc fire rfl
  obtain rfl : pc=2855 := by simpa [Lib.retPcs] using ret
  obtain ⟨u,ev,get,hit,_⟩ := MbarRing.Slot.exists_nth_countP
    (fun e : Event => Lib.finalSync e.pc) (c := 0) cnt.ge
  have uj : u<j := by
    have ub := (List.getElem?_eq_some_iff.mp get).1
    rw [List.length_take] at ub
    omega
  rw [List.getElem?_take_of_lt uj] at get
  have kind := Lib.final_kind hX (i := (g,u)) get hit (Frame.noUbBefore_of_get hX he u uj ev get)
  rcases ev with ⟨p,kd⟩
  cases kind
  exact ⟨u,p,uj,get,(final_late hp hX get).mp hit⟩

/-- Every event before the final-sync instruction in the control flow occurs
before any observed final rendezvous of its lane in the trace. -/
theorem before_final_sync {g j u p e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (last : X.get (g,u)=some ⟨p,.bar 0 none .sync⟩)
    (ord : 2≤((X.tr g).take u).countP (Execution.isBarId 0))
    (get : X.get (g,j)=some e) (nu : ∀ f, e.kind≠.ub f)
    (early : Lib.afterFinal e.pc=0) (other : Lib.finalSync e.pc=false) : j<u := by
  have hit := (final_late hp hX last).mpr ord
  have cnt := (visits hp hX get nu).trans early
  by_contra! le
  have ne : j≠u := by
    rintro rfl
    obtain rfl := Option.some.inj (get.symm.trans last)
    simp [hit] at other
  have mem : ⟨p,.bar 0 none .sync⟩ ∈ (X.tr g).take j :=
    List.mem_of_getElem? (by rw [List.getElem?_take_of_lt (by omega : u<j)]; exact last)
  exact List.countP_eq_zero.mp cnt _ mem hit

/-- All publication barriers come before the final barrier-0 rendezvous. -/
theorem final_after_b1 {g j u pc p c mode} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (last : X.get (g,u)=some ⟨p,.bar 0 none .sync⟩)
    (ord : 2≤((X.tr g).take u).countP (Execution.isBarId 0))
    (bar : X.get (g,j)=some ⟨pc,.bar 1 c mode⟩) : j<u := by
  obtain ⟨_,one|bad|bad⟩ := Lib.recorded_bar hX hp.block bar
  all_goals try cases bad.1
  have early : Lib.barOneSites.all (fun p => Lib.afterFinal p==0 && !Lib.finalSync p) = true :=
    by decide
  have facts := List.all_eq_true.mp early pc one.2.2
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at facts
  exact before_final_sync hp hX last ord bar (by simp) facts.1 facts.2

end PTX.Kernels.InklingRelDecode.Proof.Export

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.StoreValid
import Lemmas.Flow.TmemOperands

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control

private def stage : Fin 8 → Site
  | 0 => .bar22 | 1 => .shfl7 | 2 => .shfl8 | 3 => .shfl9
  | 4 => .shfl10 | 5 => .store10 | 6 => .bar23 | 7 => .ldL

set_option maxRecDepth 10000 in
private theorem predecessor {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn))
    (x : Fin 7) (site : dn.site=stage x.succ) : d.site=stage x.castSucc := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals fin_cases x <;> first | rfl | contradiction

private theorem prev_event {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ev)
    (clean : ∀ f, ev.kind≠.ub f) (x : Fin 7) (pc : ev.pc=(stage x.succ).pc) :
    ∃ u prev w ent d n, u+1=k ∧ X.get (g,u)=some prev ∧
      Frame.stateAt (thread Q L) X g u=some (some (softState w ent d n)) ∧
      d.site=stage x.castSucc := by
  have nu : ∀ pc f, ev ≠ ⟨pc,.ub f⟩ := fun _ f eq => clean f (congrArg Event.kind eq)
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he nu ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have loc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs clean
  have range : 574<ev.pc ∧ ev.pc<2331 := by rw [pc]; fin_cases x <;> decide
  obtain ⟨w,ent,d,n,rfl⟩ := (loc ▸ state_role s).softmax range.1 range.2
  change ev.pc=d.site.pc at loc
  have only (s : Site) (x : Fin 7) : s.pc=(stage x.succ).pc → s=stage x.succ := by
    revert x
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  have tag := only d.site x (loc.symm.trans pc)
  have late : d≠{} := by rintro rfl; fin_cases x <;> contradiction
  obtain ⟨u,old,cnt,prev,eq,state,get,step⟩ :=
    soft_prev (List.getElem?_eq_some_iff.mp he).1.le late hs
  exact ⟨u,prev,w,ent,old,cnt,eq,get,state,predecessor step x tag⟩

/-- The publishing sync is the immediately preceding event of each scratch load. -/
public theorem read_sync {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨2252,.rd a bs⟩) :
    ∃ u, u+1=k ∧ X.get (g,u)=some ⟨2251,.bar 0 (some 128) .sync⟩ := by
  obtain ⟨u,ev,w,ent,d,n,eq,get,hs,site⟩ := prev_event hp hX he (fun _ => nofun) 6 rfl
  have before : u < k := by omega
  obtain ⟨t,ins,o,_,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs
    (Frame.noUbBefore_of_get hX he u before ev get)
  change kernel.code[d.site.pc]?=some ins at hc
  change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev o at fire
  have pc : d.site.pc=2251 := site ▸ rfl
  rw [pc] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2251)
  have shape := fires_barSyncN_imm (id := 0) (n := 128) (by decide) (by decide)
    (by decide) (by decide) (by rw [hp.block]; decide) fire
  exact ⟨u,eq,shape ▸ get⟩

/-- The preceding store has fired in every lane recorded at the publishing sync. -/
public theorem sync_store {Q L m X g k cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨2251,.bar 0 cnt .sync⟩) :
    ∃ u a bs, u+1=k ∧ X.get (g,u)=some ⟨2250,.wr a bs⟩ := by
  obtain ⟨u,ev,w,ent,d,n,eq,get,hs,site⟩ := prev_event hp hX he (fun _ => nofun) 5 rfl
  have before : u < k := by omega
  have good := Frame.noUbBefore_of_get hX he u before ev get
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs good
  change kernel.code[d.site.pc]?=some ins at hc
  change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ev o at fire
  have pc : d.site.pc=2250 := site ▸ rfl
  rw [pc] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2250)
  obtain ⟨_,_,_,_,regs⟩ := ht
  have key : 1533 ∈ ctlLive d.site.pc := by rw [pc]; decide +kernel
  have reg := holds_mem regs (mem_factsFrom key)
  let addr := L.sharedBase+212992+(g%L.block/32%4)*4
  have bound := hp.sharedRange
  change L.sharedBase+213340≤2^18 at bound
  have small : addr<2^32 := by dsimp [addr]; omega
  change t.regs 1533=some (b32 (addr%2^32)) at reg
  rw [Nat.mod_eq_of_lt small] at reg
  generalize Assumptions.all = A at fire
  have shape := fires_stv32_kind (A := A) (g := g) (L := L) (pc := 2250) (ik := .b)
    (srcs := [.reg 1534]) (e := ev) (o := o) reg small (.inl rfl)
  have loc := EventFrame.fires_source_pc fire
  generalize eventTmpl A L g t _ = tmpl at shape fire
  rcases shape (by assumption) with ⟨a,bs,kind⟩|⟨f,bad⟩
  · obtain ⟨p,kd⟩ := ev
    change p=2250 at loc
    cases loc
    cases kind
    exact ⟨u,a,bs,eq,get⟩
  · exact (good f bad).elim

/-- From any publication to a later scratch store of the same lane there
is an intervening counted sync at pc 2241. Walk the four shuffle events
backwards from the store; none of them can be the earlier publication. -/
public theorem scratch_separated {Q L m X g i k a bs c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (first : X.IsBarrier (g,i) 0 c 2251) (lt : i<k)
    (store : X.get (g,k)=some ⟨2250,.wr a bs⟩) :
    ∃ j, i<j ∧ j<k ∧ X.IsBarrier (g,j) 0 (some 128) 2241 := by
  have backwards (n : Nat) (hn : n<5) {t ev} (get : X.get (g,t)=some ev)
      (cl : ∀ f, ev.kind≠.ub f) (pc : ev.pc=(stage (⟨n,by omega⟩ : Fin 7).succ).pc)
      (it : i<t) : ∃ j, i<j ∧ j<t ∧ X.IsBarrier (g,j) 0 (some 128) 2241 := by
    induction n generalizing t ev with
    | zero =>
      obtain ⟨u,prev,w,ent,d,cnt,rfl,old,state,site⟩ := prev_event hp hX get cl 0 pc
      have clean := Frame.noUbBefore_of_get hX get u (Nat.lt_succ_self _) prev old
      obtain ⟨_,ins,_,_,_,fetch,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg)
        hX old state clean
      change kernel.code[d.site.pc]?=some ins at fetch
      change Fires d.site.pc _ prev _ at fire
      have pos : d.site.pc=2241 := site ▸ rfl
      rw [pos] at fetch fire
      obtain rfl := Option.some.inj (fetch.symm.trans Flow.code_2241)
      have kind := fires_barSyncN_imm (id := 0) (n := 128) (by decide) (by decide)
        (by decide) (by decide) (by rw [hp.block]; decide) fire
      cases kind
      refine ⟨u,?_,Nat.lt_succ_self _,old⟩
      have ne : i≠u := by
        rintro rfl
        change X.get _=_ at first
        rw [old] at first
        cases first
      omega
    | succ n ih =>
      obtain ⟨u,prev,w,ent,d,cnt,rfl,old,state,site⟩ :=
        prev_event hp hX get cl ⟨n+1,by omega⟩ pc
      have clean := Frame.noUbBefore_of_get hX get u (Nat.lt_succ_self _) prev old
      have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX old state clean
      change prev.pc=d.site.pc at pos
      rw [site] at pos
      have iu : i<u := by
        have ne : i≠u := by
          rintro rfl
          change X.get _=_ at first
          rw [old] at first
          cases first
          have bounds : ∀ z : Fin 7, z.val<5 → (stage z.castSucc).pc<2251 := by decide
          have := bounds ⟨n+1,by omega⟩ hn
          change 2251=_ at pos
          omega
        omega
      obtain ⟨j,ij,ju,bar⟩ := ih (by omega) old clean pos iu
      exact ⟨j,ij,by omega,bar⟩
  exact backwards 4 (by decide) store (fun _ => nofun) rfl lt

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

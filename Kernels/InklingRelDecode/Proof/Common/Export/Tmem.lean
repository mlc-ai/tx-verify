-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Tmem.Tmem1Protocol
import Kernels.InklingRelDecode.Proof.Common.ResourceCount
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Common.BaseWord
import Lemmas.Flow.UbStop
import all Kernels.InklingRelDecode.Proof.Common.LaunchLane
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Flow.Code.Part044

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Tmem.Pair PTX.Proof

private theorem initial {L g d p grp dst act}
    (inv : Startup.Inv L g d) (active : Startup.enterOf d=none)
    (ev : Startup.Ev L g d ⟨p,.tc (.resource grp dst act)⟩) :
    g%L.block<32 ∧ grp=.one ∧ TmemShape (Startup.resourceCount (g%L.block) d.site) act := by
  obtain ⟨s,t,x,w⟩ := d
  cases s
  case enter => cases active
  case allocWr => obtain ⟨_,_,h⟩ := ev; cases h
  case ld0 => obtain ⟨_,_,h,_⟩ := ev; cases h
  case shfl => obtain ⟨_,_,h⟩ := ev; cases h
  case bar0 => cases ev
  case bar1 => cases ev
  all_goals
    have low := inv (by simp)
    cases ev
    exact ⟨low,rfl,by simp [Startup.resourceCount,Nat.not_le_of_lt low,TmemShape]⟩

private theorem operation {Q L m X g k p grp dst act} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨p,.tc (.resource grp dst act)⟩) :
    g%L.block/32=0 ∧ grp=.one ∧ TmemShape (tmemOps ((X.tr g).take k)) act ∧
      (Iface.BaseRead L X → ∀ a n, act=.dealloc a n → a=0) := by
  obtain ⟨s,hs,_⟩ := good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ _ h => by cases h) (hf g hg k)
  have hu := noUbBefore_of_get hX he
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have hi := (reached_table hf hg hu hs).1
  have pc := event_pcU (fun g h => thread_sound hp h) hX he hs (by simp)
  change p=_ at pc
  obtain ⟨d,n⟩ := s
  rcases d with d|⟨r,d⟩
  · obtain ⟨low,rfl,sh⟩ := initial hi.1 (Code.gatedExit_none.mp hi.2)
      (start_ev hp hX he hs (by simp))
    rw [resource_prefix hp hX hf hg low hk hu hs]
    refine ⟨by omega,rfl,sh,?_⟩
    intro _ a n req
    subst act
    have ev := start_ev hp hX he hs (by simp)
    have active := Code.gatedExit_none.mp hi.2
    obtain ⟨site,t,x,w⟩ := d
    cases site <;> simp_all [Startup.resourceCount,TmemShape,Nat.not_le_of_lt low]
    · obtain ⟨_,_,eq⟩ := ev; cases eq
    · cases active
  · rcases r with (r|r)
    · cases r with
      | dispatch => cases worker_no_resource hp hX hf he (by simp) hs
      | prologue w =>
        have kind := data_resource hp hX he (by simp) hs
        have raw := of_decide_eq_true kind.symm
        have pos : p=2851 := pc.trans raw
        obtain ⟨_,e,s,_,eq⟩ := (pc ▸ state_role _).epilogue (by omega) (by omega) hi
        cases eq
        change p=s.site.pc at pc
        have site : s.site=.dealloc := by
          have h := pc.symm.trans pos
          revert h
          generalize s.site=st
          cases st <;> repeat' first | decide +kernel | (rename_i j; revert j)
        obtain ⟨st,v⟩ := s
        change st=.dealloc at site
        subst st
        have low : g%L.block<32 := hi
        obtain ⟨t,ins,o,ht,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX he hs
          (by simp)
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2851)
        obtain ⟨a,rfl,rfl,rfl,addr⟩ := Epilogue.dealloc_kind fire rfl
        rw [resource_prefix hp hX hf hg low hk hu hs]
        refine ⟨by omega,rfl,⟨_,rfl⟩,?_⟩
        intro base _ _ req
        cases req
        have word : e.base=PTX.Proof.b32 0 := recorded_zero hp hX base hk hu hs
        obtain ⟨_,_,_,_,regs⟩ := ht
        have reg := holds_mem regs (mem_factsFrom
          (val := Epilogue.Control.valueOf (epiEntry e (g%L.block)) L g v)
          (show 463 ∈ Epilogue.Control.ctlLive 2851 by decide +kernel))
        change t.regs 463=some e.base at reg
        rw [word] at reg
        rw [readBits_b32' reg] at addr
        cases addr
        rfl
    · exact (launch_lane hp hX hk hs).elim

/-- Each warp-zero resource trace allocates, relinquishes and deallocates in order. -/
public theorem tmem_ops {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : Tmem.One.Tmem1Ops L X 0 := by
  refine ⟨by rw [hp.block]; decide,?_⟩
  intro g k p grp dst act hg he
  obtain ⟨hw,hg,shape,_⟩ := operation hp hX hf hg he
  exact ⟨hw,hg,shape⟩

public theorem dealloc_zero {Q L m X g k p grp dst a n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (base : Iface.BaseRead L X)
    (hg : g<L.threads) (he : X.get (g,k)=some ⟨p,.tc (.resource grp dst (.dealloc a n))⟩) :
    a=0 := by
  obtain ⟨_,_,_,zero⟩ := operation hp hX hf hg he
  exact zero base a n rfl

/-- A return of a warp-zero lane has all three resource requests in its prefix. -/
public theorem exit_ops {Q L m X g k p} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : g<L.threads) (warp : g%L.block/32=0)
    (he : X.get (g,k)=some ⟨p,.exit⟩) : tmemOps ((X.tr g).take k)=3 := by
  obtain ⟨s,hs,_⟩ := good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ _ h => by cases h) (hf g hg k)
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have low : g%L.block<32 := by omega
  rw [resource_prefix hp hX hf hg low hk (noUbBefore_of_get hX he) hs]
  obtain ⟨_,_,_,_,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX he hs (by simp)
  have ret := Lib.ret_pc' hc fire rfl
  simp only [Lib.retPcs,List.mem_singleton] at ret
  obtain ⟨d,n⟩ := s
  rcases d with d|⟨r,d⟩
  · change d.site.pc=2855 at ret
    exfalso
    revert ret
    generalize d.site=site
    cases site <;> first | decide | (rename_i r; cases r <;> decide)
  · rcases r with (r|r)
    · cases r with
      | dispatch =>
        have high := (worker_warp hp hX hk hs).1
        change 128≤g%L.block at high
        omega
      | prologue =>
        rcases d with d|⟨e,d|⟨_,d⟩⟩
        · change d.site.pc=2855 at ret
          have bound := d.site.pc_range
          omega
        · change d.site.pc=2855 at ret
          rcases d.site.pc_range with range|range
          · omega
          · rw [range] at ret; contradiction
        · change 2+(decide (d.site.pc=2855)).toNat=3
          rw [decide_eq_true ret]
          rfl
    · exact (launch_lane hp hX hk hs).elim

public theorem tmem_facts {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) : Tmem.One.Tmem1Facts L X 0 :=
  ⟨tmem_ops hp hX hf,dealloc_zero hp hX hf base,exit_ops hp hX hf⟩

end PTX.Kernels.InklingRelDecode.Proof.Export

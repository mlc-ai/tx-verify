-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.OccursSite
import Kernels.InklingRelDecode.Proof.Common.EndTime
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.ResourceSites
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Lemmas.Flow.TmemOperands

/-! # The allocation's successor

An allocation request is the startup's first event: lane 0 of its warp then stores the result
(the allocation's second sub-step), another lane reads it back after the barrier. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Startup.Export
open PTX PTX.Flow PTX.Proof

private theorem alloc_start {L g d p grp dst n} (active : Startup.enterOf d = none)
    (ev : Startup.Ev L g d ⟨p,.tc (.resource grp dst (.alloc n))⟩) : d.site = .alloc := by
  obtain ⟨s,t,x,w⟩ := d
  cases s
  case enter => cases active
  case allocWr => obtain ⟨_,_,h⟩ := ev; cases h
  case ld0 => obtain ⟨_,_,h,_⟩ := ev; cases h
  case shfl => obtain ⟨_,_,h⟩ := ev; cases h
  case bar0 => cases ev
  case bar1 => cases ev
  case alloc => rfl
  case relinq => cases ev

private theorem no_alloc {L g t p grp dst n o}
    (fire : Fires p (eventTmpl Assumptions.all L g t (.tcDealloc .one (.reg 463) (.imm 512)))
      ⟨p,.tc (.resource grp dst (.alloc n))⟩ o) : False := by
  obtain ⟨_,_,_,_,req⟩ := fires_tcDealloc_ops fire rfl
  cases req

private theorem alloc_state {Q L m X g k pc grp dst n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.resource grp dst (.alloc n))⟩) :
    (⟨pc,.tc (.resource grp dst (.alloc n))⟩ : Event) = ⟨11,.tc (.resource .one
      (some ⟨.shared,g/L.block,L.sharedBase⟩) (.alloc 512))⟩ ∧
    ∃ tm x w c, Frame.stateAt (thread Q L) X g k = some (some (.inl ⟨.alloc,tm,x,w⟩,c)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have hres := Export.tmem_event_pc hX he rfl
  have pcm := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change pc = (thread Q L g).pc s at pcm
  simp only [Lib.resPcs,List.mem_cons,List.not_mem_nil,or_false] at hres
  have low : pc < 27 := by
    by_contra big
    exfalso
    obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g h => thread_sound hp h) hX he hs
      (by simp)
    rw [← pcm] at hc fire
    rcases hres with rfl|rfl|rfl|rfl
    · omega
    · omega
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2851)
      exact no_alloc fire
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2854)
      exact no_alloc fire
  obtain ⟨⟨site,tm,x,w⟩,n0,rfl⟩ := (pcm ▸ state_role s).startup low
  have ev := start_ev hp hX he hs (by simp)
  have hi := (reached_table hf hg (Frame.noUbBefore_of_get hX he) hs).1
  have is : site = .alloc := alloc_start (Code.gatedExit_none.mp hi.2) ev
  subst is
  exact ⟨ev,tm,x,w,n0,hs⟩

/-- **An allocation request is the startup's**: its shape is the allocation's. -/
public theorem alloc_event {Q L m X g k pc grp dst n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.resource grp dst (.alloc n))⟩) :
    pc = 11 ∧ grp = .one ∧ dst = some ⟨.shared,g/L.block,L.sharedBase⟩ ∧ n = 512 := by
  have := (alloc_state hp hX hf he).1
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq, Tmem.Request.alloc.injEq] at this
  tauto

private theorem alloc_next {Q L m X g k pc grp dst n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.resource grp dst (.alloc n))⟩) :
    ∃ d c, Frame.stateAt (thread Q L) X g (k+1) = some (some (.inl d,c)) ∧
      d.site = if laneOf L g = 0 then .allocWr else .bar0 := by
  obtain ⟨-,tm,x,w,c,hs⟩ := alloc_state hp hX hf he
  rw [Frame.stateAt_succ (show (X.tr g)[k]? = some _ from he), hs]
  have step : Startup.succ L g ⟨.alloc,tm,x,w⟩ ⟨pc,.tc (.resource grp dst (.alloc n))⟩ =
      some (some ⟨if laneOf L g = 0 then .allocWr else .bar0,tm,x,w⟩) := by
    simp only [Startup.succ]; split_ifs <;> rfl
  refine ⟨_,_,to_state step ?_,rfl⟩
  split_ifs <;> rfl

/-- **Lane 0's event after its allocation** is the store of the result word. -/
public theorem alloc_next_wr {Q L m X g k pc grp dst n f} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.resource grp dst (.alloc n))⟩) (hl : laneOf L g = 0)
    (hn : X.get (g,k+1) = some f) (hu : ∀ u, f.kind ≠ .ub u) :
    ∃ bytes, f = ⟨pc,.wr { loc := ⟨.shared,g/L.block,L.sharedBase⟩, size := 4 } bytes⟩ := by
  obtain ⟨d,c,hs,site⟩ := alloc_next hp hX hf he
  simp only [hl, ↓reduceIte] at site
  have ev := start_ev hp hX hn hs hu
  obtain ⟨st,t,x,w⟩ := d
  change st = .allocWr at site
  subst st
  obtain ⟨col,-,rfl⟩ := ev
  obtain ⟨rfl,-⟩ := alloc_event hp hX hf he
  exact ⟨_,rfl⟩

/-- **The instruction after lane 0's allocation request** is at pc 11, the allocation's second
step: the event the lane performs next (in the trace or about to be) is at pc 11. -/
public theorem alloc_next_pc {Q L m X g k pc grp dst n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.resource grp dst (.alloc n))⟩) (hl : laneOf L g = 0)
    (hn : Occurs L X g (k+1) ev) (hu : ∀ f, ev.kind ≠ .ub f) : ev.pc = 11 := by
  obtain ⟨d,c,hs,site⟩ := alloc_next hp hX hf he
  simp only [hl, ↓reduceIte] at site
  obtain ⟨s,hs',hpc,-⟩ := hn.site hp hX hf hu
  rw [hs] at hs'
  obtain rfl := Option.some.inj (Option.some.inj hs')
  obtain ⟨st,t,x,w⟩ := d
  change st = .allocWr at site
  subst st
  exact hpc

/-- **Lane 0 after its allocation is earlier than another lane after its own.** -/
public theorem alloc_earlier {Q L m X h g kh kg ph pg nh ng grh grg dh dg}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hah : X.get (h,kh)=some ⟨ph,.tc (.resource grh dh (.alloc nh))⟩)
    (hlh : (X.tr h).length = kh+1) (hl0 : laneOf L h = 0)
    (hag : X.get (g,kg)=some ⟨pg,.tc (.resource grg dg (.alloc ng))⟩)
    (hlg : (X.tr g).length = kg+1) (hl : laneOf L g ≠ 0) :
    Sched.threadTime (schedule Q L) X h < Sched.threadTime (schedule Q L) X g := by
  obtain ⟨d1,c1,s1,site1⟩ := alloc_next hp hX hf hah
  obtain ⟨d2,c2,s2,site2⟩ := alloc_next hp hX hf hag
  rw [← hlh] at s1
  rw [← hlg] at s2
  simp only [hl0, ↓reduceIte] at site1
  simp only [hl, ↓reduceIte] at site2
  rw [end_time s1, end_time s2, (siteTime_startup d1 c1).2.1 site1,
    (siteTime_startup d2 c2).2.2 site2]
  decide

end PTX.Kernels.InklingRelDecode.Proof.Startup.Export

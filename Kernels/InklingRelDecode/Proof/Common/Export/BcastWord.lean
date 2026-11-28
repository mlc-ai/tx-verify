-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.FollowStartup
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.Export.BcastExit
import Kernels.InklingRelDecode.Proof.Common.Export.PshRecv
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Kernel.FrameU

/-! # The broadcast word names the warp

A data lane that received the warp-index broadcast of a Softmax round (pc 1261) or of the epilogue
(pc 2603) received the warp index of its warp (`bcast_names`): the source of the index shuffle is
lane zero of the warp, whose shuffle of the same ordinal is at the same pc (or is a prologue
broadcast, which sends the warp index too) and sends the register that holds the warp index. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

private theorem soft_operand {Q L m X g k mode a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ⟨1261,.shfl mode a b c recv ok⟩) : a=b32 (g%L.block/32) := by
  have clean : ∀ f, (Event.mk 1261 (.shfl mode a b c recv ok)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<1261; decide)
    (by show 1261<2331; decide)
  change 1261=d.site.pc at pc
  obtain ⟨t,ins,o,ht,-,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs
    (fun _ => nofun)
  obtain ⟨-,-,-,-,regs⟩ := ht
  change kernel.code[d.site.pc]?=some ins at hc
  rw [←pc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1261)
  change Fires d.site.pc _ _ o at fire
  rw [←pc] at fire
  obtain ⟨same,-,-,-⟩ := Lib.shfl_operand (n := 0) rfl rfl fire rfl
  have reg := holds_mem regs (mem_factsFrom
    (show 464 ∈ Softmax.Control.ctlLive d.site.pc by rw [←pc]; decide))
  change t.regs 464=some (Softmax.Control.valueOf ent L g d 464) at reg
  exact Option.some.inj (same.symm.trans reg)

private theorem epi_at {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ev) (clean : ∀ f, ev.kind≠.ub f) (pc : ev.pc=2603) :
    ∃ w ent d n, Frame.stateAt (thread Q L) X g k=some (some (epiState w ent d n)) ∧
      d.site.pc=2603 := by
  have hg := Frame.lt_of_get hX get
  have nu := Frame.noUbBefore_of_get hX get
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True)
    (fun g hg => thread_sound hp hg) hX get (fun _ f h => clean f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have loc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get hs clean
  have loc' : (2603:Nat)=(thread Q L g).pc s := pc ▸ loc
  have pl : Placement s 2603 := by rw [loc']; exact state_role s
  obtain ⟨w,ent,d,n,rfl⟩ := pl.epilogue (by omega) (by omega) (reached_table hf hg nu hs).1
  exact ⟨w,ent,d,n,hs,loc'.symm⟩

private theorem epi_operand {Q L m X g k mode a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨2603,.shfl mode a b c recv ok⟩) : a=b32 (g%L.block/32) := by
  obtain ⟨w,ent,d,n,hs,pc⟩ := epi_at hp hX hf get (fun _ => nofun) rfl
  obtain ⟨t,ins,o,ht,-,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs
    (fun _ => nofun)
  obtain ⟨-,-,-,-,regs⟩ := ht
  change kernel.code[d.site.pc]?=some ins at hc
  rw [pc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2603)
  change Fires d.site.pc _ _ o at fire
  rw [pc] at fire
  obtain ⟨same,-,-,-⟩ := Lib.shfl_operand (n := 0) rfl rfl fire rfl
  have reg := holds_mem regs (mem_factsFrom
    (show 464 ∈ Epilogue.Control.ctlLive d.site.pc by rw [pc]; decide))
  change t.regs 464=some (Epilogue.Control.valueOf (epiEntry ent (g%L.block)) L g d.received 464)
    at reg
  exact Option.some.inj (same.symm.trans reg)

private theorem psh_word {Q L m X q j pc' a' b' c' r' o'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (q,j)=some ⟨pc',.shfl .idx a' b' c' r' o'⟩) (psh : pc'∈[202,244,286]) :
    a'=b32 (q%L.block/32) := by
  obtain ⟨_,_,e⟩ := psh_event hp hX get (fun _ => nofun) psh
  simpa using congrArg (fun ev => match ev.kind with | .shfl _ a _ _ _ _ => a | _ => a') e

private theorem epi_site (s : Epilogue.Site) (h : s.pc=2603) : s=.shfl := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_pc (s : Epilogue.Site) (h : s.pc∈Lib.shflPcs) : s.pc=2603 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem round_lt (s : Softmax.Site) (i : Nat) (shuf : s.isShuffle=true)
    (prev : Softmax.needsPrevious s = true → 0 < i) :
    Lib.shflBase i + Softmax.shflInRound s i < Lib.shflBase (i+1) := by
  cases s <;> simp only [Softmax.Site.isShuffle] at shuf <;> try contradiction
  all_goals simp only [Softmax.needsPrevious] at prev
  all_goals simp only [Softmax.shflInRound,Lib.shflBase]
  all_goals split <;> split <;> first | omega | (have := prev trivial; omega)

private theorem shuffle_of (s : Softmax.Site) (h : s.pc∈Lib.shflPcs) : s.isShuffle=true := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem loop_below {ent : Softmax.Control.Entry} {t : Nat} {d : Softmax.Control.D}
    (inv : Softmax.Control.Inv ent t d) (shuf : d.site.isShuffle=true) : d.i<ent.limit := by
  have key : ∀ s : Softmax.Site, s.isShuffle=true →
      s≠.epilogue ∧ s≠.setMaxReg ∧ s≠.bar0 ∧ ∀ j, s≠.pre j := by
    intro s h
    cases s <;> simp_all [Softmax.Site.isShuffle]
  obtain ⟨h1,h2,h3,h4⟩ := key _ shuf
  exact inv.loop h1 h2 h3 h4

set_option maxRecDepth 10000 in
/-- The partner of the epilogue's broadcast sends the warp index of its own warp. -/
private theorem epi_partner {Q L m X g k q j pc' mode a b c recv ok a' b' c' r' o'}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨2603,.shfl mode a b c recv ok⟩)
    (low : q%L.block<128) (cta : q/L.block=g/L.block)
    (get' : X.get (q,j)=some ⟨pc',.shfl .idx a' b' c' r' o'⟩)
    (count : ((X.tr q).take j).countP Execution.isShfl=
      ((X.tr g).take k).countP Execution.isShfl) : a'=b32 (q%L.block/32) := by
  have cleanj : ∀ f, (Event.mk pc' (.shfl .idx a' b' c' r' o')).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,dpc⟩ := epi_at hp hX hf get (fun _ => nofun) rfl
  have hg := Frame.lt_of_get hX get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  have exact := (shfl_epi hp hX len hs nu).1 (Or.inr (epi_site _ dpc))
  have cnt : n .shfl=((X.tr g).take k).countP Execution.isShfl := fcount hs _
  have lim := reached_limit hp hX hg len hs
  have hq := Frame.lt_of_get hX get'
  have lenj := (List.getElem?_eq_some_iff.mp get').1.le
  have nuj := Frame.noUbBefore_of_get hX get'
  have listed : pc'∈Lib.shflPcs := by
    have := Lib.shfl_event hX get' (fun _ => nofun)
    simpa [Execution.isShfl] using this
  obtain ⟨sj,hsj,_⟩ := Frame.good_stateU (J := fun _ _ => True)
    (fun g hg => thread_sound hp hg) hX get' (fun _ f h => cleanj f (congrArg Event.kind h))
    ⟨control_tracked hp hX q j hq,fun _ _ => trivial⟩
  have locj := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get' hsj cleanj
  have cj : ((X.tr q).take j).countP Execution.isShfl=
      1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase ent.limit := by
    rw [count,←cnt,exact]
  have cls : pc'∈[202,244,286] ∨ pc'<27 ∨ (574<pc' ∧ pc'<2331) ∨ (pc'=2464 ∨ pc'=2512) ∨
      pc'=2603 := by
    simp only [Lib.shflPcs,List.mem_cons,List.not_mem_nil,or_false] at listed ⊢
    omega
  rcases cls with psh|st|soft|work|epi
  · exact psh_word hp hX get' psh
  · exfalso
    obtain ⟨t,n2,rfl⟩ := (locj ▸ state_role sj).startup (by change pc'<27; omega)
    have one := shfl_startup_exact hp hX lenj hsj nuj
    have c2 : n2 .shfl=((X.tr q).take j).countP Execution.isShfl := fcount hsj _
    obtain ⟨st,tt,xx,ww⟩ := t
    cases st with
    | enter r =>
      change pc'=Startup.Entry.pc r at locj
      subst locj
      cases r <;> revert listed <;> decide
    | _ => dsimp only at one; omega
  · exfalso
    obtain ⟨w2,ent2,d2,n2,hs2,pc2⟩ := at_site hp hX get' cleanj soft.1 soft.2
    have o := shfl_ordinal hp hX lenj hs2 nuj
    have c2 : n2 .shfl=((X.tr q).take j).countP Execution.isShfl := fcount hs2 _
    have lim2 := reached_limit hp hX hq lenj hs2
    have inv := (reached_table hf hq nuj hs2).1.1
    have shuf := shuffle_of d2.site (pc2 ▸ listed)
    have below := loop_below inv shuf
    have lt := round_lt d2.site d2.i shuf (shfl_previous hp hX lenj hs2 nuj)
    have mono : Lib.shflBase (d2.i+1)≤Lib.shflBase ent2.limit := by
      unfold Lib.shflBase
      split <;> split <;> omega
    have pre : Iface.preloadCount Q L (q/L.block)=Iface.preloadCount Q L (g/L.block) := by
      rw [cta]
    have lims : ent2.limit=ent.limit := by rw [lim2,lim,cta]
    simp only [Softmax.shflCount] at o
    have e1 := c2.trans cj
    rw [lims] at mono
    omega
  · exfalso
    obtain ⟨w2,x2,r2,d2,n2,hs2,-⟩ := worker_event hp hX hf get' cleanj
      (by change 2344<pc'; omega) (by change pc'<2557; omega) (by change pc'≠2422; omega)
    have := worker_warp hp hX lenj hs2
    dsimp only at this
    omega
  · subst epi
    exact epi_operand hp hX hf get'

/-- **The word a warp-index broadcast delivered names the warp**: a data lane that made the
Softmax round's broadcast (pc 1261) or the epilogue's (pc 2603) as its `n`-th shuffle received the
warp index of its warp. -/
public theorem bcast_names {Q L m X g n P w} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (site : P=1261 ∨ P=2603) (at_ : Lib.ShflAt X g P n w) (lane : g%L.block<128) :
    w=b32 (g%L.block/32) := by
  obtain ⟨j,a,ok,get,cnt⟩ := at_
  have hb32 : L.block%32=0 := by rw [hp.block]
  have hg := Frame.lt_of_get hX get
  have hz : (shflSource .idx (laneOf L g) 0 31).1=0 := by simp [shflSource]
  have srcl := Step.shflSource_lt ShflMode.idx
    (show laneOf L g<32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨hh,hw,hcta,hlane,_⟩ := Frame.lane_facts hb32 hg rfl srcl
  rw [hz] at hh hw hcta hlane
  have lowh : (g-laneOf L g+0)%L.block<128 := by rw [hp.block] at hw lane ⊢; omega
  obtain ⟨-,src|ex⟩ := hX.shfl g j n P .idx a 0 31 w ok get ⟨⟨_,_,_,_,_,_,_,get⟩,cnt⟩
  swap
  · rw [hz] at ex
    exact (bcast_not_exited hp hX hf site get cnt lowh hcta ex).elim
  obtain ⟨j1,p',b',c',r',o',rank,got⟩ := src
  rw [hz] at got rank
  have count := rank.2.trans cnt.symm
  rw [←hw]
  rcases site with rfl|rfl
  · rcases Softmax.Export.partner_site hp hX hf get (Or.inl rfl) lowh hcta got count with h|h
    · subst h
      exact soft_operand hp hX got
    · exact psh_word hp hX got h
  · exact epi_partner hp hX hf get lowh hcta got count

end PTX.Kernels.InklingRelDecode.Proof.Export

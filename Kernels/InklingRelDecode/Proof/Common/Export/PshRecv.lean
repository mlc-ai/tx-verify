-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.Regs
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.FollowStartup
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Prologue.Export.BroadcastAt
import Kernels.InklingRelDecode.Proof.Prologue.PreloadCount
import Kernels.InklingRelDecode.Proof.Softmax.Export.ExitShuffles
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
import Lemmas.Kernel.FrameU

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

private theorem startup_shfl (s : Startup.Site) (h : s.pc=17) : s=.shfl := by
  revert h
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem psh_site (s : Prologue.Site) (h : s.pc∈[202,244,286]) : ∃ b, s=.psh b := by
  revert h
  cases s <;> first | exact fun _ => ⟨_,rfl⟩ |
    (repeat' first | decide +kernel | (rename_i j; revert j))

/-- **A prologue broadcast sends the warp index**: the event at a broadcast site is an index
shuffle of lane zero of the operand `warp`. -/
public theorem psh_event {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ev) (clean : ∀ f, ev.kind≠.ub f) (site : ev.pc ∈ [202,244,286]) :
    ∃ recv ok, ev=⟨ev.pc,.shfl .idx (b32 (g%L.block/32)) 0 31 recv ok⟩ :=
  Prologue.Export.psh_shape hp hX get clean site

/-- **A prologue broadcast delivers the warp index.** The source lane's shuffle of the same
ordinal is a prologue broadcast too (the startup shuffle has ordinal zero, every other shuffle
of the same ordinal belongs to a later role), and each sends its own warp index. -/
public theorem psh_recv {Q L m X g k pc a recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.shfl .idx a 0 31 recv ok⟩) (site : pc∈[202,244,286]) :
    recv=b32 (g%L.block/32) := by
  have clean : ∀ f, (Event.mk pc (.shfl .idx a 0 31 recv ok)).kind≠.ub f := fun _ => nofun
  have hg := Frame.lt_of_get hX he
  have len := (List.getElem?_eq_some_iff.mp he).1.le
  have nu := Frame.noUbBefore_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f h => clean f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs clean
  have region : 27<pc ∧ pc<574 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,d,n,rfl⟩ := (pos ▸ state_role s).prologue region.1 region.2
  change pc=d.site.pc at pos
  obtain ⟨b,hb⟩ := psh_site d.site (pos ▸ site)
  have ordinal := shfl_prologue hp hX len hs nu
  have count : n .shfl=((X.tr g).take k).countP Execution.isShfl := fcount hs _
  rw [hb] at ordinal
  have mine : ((X.tr g).take k).countP Execution.isShfl=1+b.val := by
    rw [←count, ordinal]; rfl
  obtain ⟨low,hist⟩ := (reached_table hf hg nu hs).2
  have cap : min 3 (Prologue.Control.preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d) =
      Iface.preloadCount Q L (g/L.block) := by
    have lo : 180≤d.site.pc := by rw [hb]; fin_cases b <;> decide
    exact Prologue.preload_count hp hg (hist.known.first (by omega))
      (hist.known.last (by omega)) (hist.known.seq (by omega))
  have blk : b.val<Iface.preloadCount Q L (g/L.block) := by
    rw [←cap]
    exact lt_min b.isLt (hist.block b (by rw [hb]; rfl))
  have hbl : L.block=256 := hp.block
  have hb32 : L.block%32=0 := by rw [hbl]
  have hz : (shflSource .idx (laneOf L g) 0 31).1=0 := by simp [shflSource]
  have srcl := Step.shflSource_lt ShflMode.idx
    (show laneOf L g<32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨hh,hw,hcta,hlane,_⟩ := Frame.lane_facts hb32 hg rfl srcl
  rw [hz] at hh hw hcta hlane
  obtain ⟨-,src|ex⟩ := hX.shfl g k _ pc .idx a 0 31 recv ok he ⟨⟨_,_,_,_,_,_,_,he⟩,rfl⟩
  swap
  · obtain ⟨v,pc',exit,small⟩ := ex
    rw [hz] at exit
    have lowh : (g-laneOf L g+0)%L.block<128 := by rw [hbl] at hw low ⊢; omega
    obtain ⟨total,-⟩ := Softmax.Export.exit_shuffles hp hX exit lowh
    rw [hcta] at total
    dsimp only at small
    rw [hz] at small
    exfalso
    omega
  obtain ⟨j,p',b',c',r',o',rank,get⟩ := src
  rw [hz] at get rank
  have lenj := (List.getElem?_eq_some_iff.mp get).1.le
  have nuj := Frame.noUbBefore_of_get hX get
  have cleanj : ∀ f, (Event.mk p' (.shfl .idx recv b' c' r' o')).kind≠.ub f := fun _ => nofun
  have ordj : ((X.tr (g-laneOf L g+0)).take j).countP Execution.isShfl=1+b.val :=
    rank.2.trans mine
  have inpcs : p'∈Lib.shflPcs := by
    simpa [Execution.isShfl] using (Lib.shfl_event hX get cleanj).symm
  have cls : p'∈[202,244,286] ∨ p'=17 ∨ (574<p' ∧ p'<2331) ∨ p'=2464 ∨ p'=2512 ∨ p'=2603 := by
    simp only [Lib.shflPcs,List.mem_cons,List.not_mem_nil,or_false] at inpcs ⊢
    omega
  have lowh : (g-laneOf L g+0)%L.block<128 := by rw [hbl] at hw low ⊢; omega
  have stJ : ∃ sj, Frame.stateAt (thread Q L) X (g-laneOf L g+0) j=some (some sj) ∧
      (Event.mk p' (.shfl .idx recv b' c' r' o')).pc=(thread Q L (g-laneOf L g+0)).pc sj := by
    obtain ⟨sj,hsj,_⟩ := Frame.good_stateU (J := fun _ _ => True)
      (fun g hg => thread_sound hp hg) hX get (fun _ f h => cleanj f (congrArg Event.kind h))
      ⟨control_tracked hp hX (g-laneOf L g+0) j hh,fun _ _ => trivial⟩
    exact ⟨sj,hsj,Frame.event_pcU (fun g hg => thread_sound hp hg) hX get hsj cleanj⟩
  obtain ⟨sj,hsj,locj⟩ := stJ
  rcases cls with psh|st|soft|m1|m2|epi
  · obtain ⟨r1,o1,hev⟩ := Prologue.Export.psh_shape hp hX get cleanj psh
    have kind := congrArg Event.kind hev
    simp only [Kind.shfl.injEq] at kind
    rw [kind.2.1,hw]
  · exfalso
    obtain ⟨t,n2,rfl⟩ := (locj ▸ state_role sj).startup (by change p'<27; omega)
    change p'=t.site.pc at locj
    have site := startup_shfl t.site (by omega)
    have z : ((X.tr (g-laneOf L g+0)).take j).countP Execution.isShfl=0 :=
      startup_ordinal hp hX lenj (by simp [Startup.enterOf,site]) hsj
    omega
  · exfalso
    obtain ⟨w2,ent,d2,n2,hs2,pc2⟩ := at_site hp hX get cleanj soft.1 soft.2
    have o := shfl_ordinal hp hX lenj hs2 nuj
    have c2 : n2 .shfl=((X.tr (g-laneOf L g+0)).take j).countP Execution.isShfl := fcount hs2 _
    rw [hcta] at o
    have e3 := c2.trans ordj
    rw [e3] at o
    have := Nat.zero_le (Softmax.shflCount d2)
    omega
  · exfalso
    obtain ⟨w2,x2,r2,d2,n2,hs2,-⟩ := worker_event hp hX hf get cleanj
      (by change 2344<p'; omega) (by change p'<2557; omega) (by change p'≠2422; omega)
    have := worker_warp hp hX lenj hs2
    dsimp only at this
    omega
  · exfalso
    obtain ⟨w2,x2,r2,d2,n2,hs2,-⟩ := worker_event hp hX hf get cleanj
      (by change 2344<p'; omega) (by change p'<2557; omega) (by change p'≠2422; omega)
    have := worker_warp hp hX lenj hs2
    dsimp only at this
    omega
  · exfalso
    have hi := (reached_table hf hh nuj hsj).1
    obtain ⟨w2,ent,d2,n2,rfl⟩ := (locj ▸ state_role sj).epilogue (by change 2565≤p'; omega)
      (by change p'<2853; omega) hi
    have o := shfl_epilogue hp hX lenj hsj nuj
    have c2 : n2 .shfl=((X.tr (g-laneOf L g+0)).take j).countP Execution.isShfl := fcount hsj _
    rw [hcta] at o
    omega

end PTX.Kernels.InklingRelDecode.Proof.Export

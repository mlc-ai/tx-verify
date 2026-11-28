-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.TcState
public import Kernels.InklingRelDecode.Proof.Lib.Dissent
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Softmax.Export.PredBar
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Proof.Softmax.RescaleChoice
import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Tmem.Pair Control TcState

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The lane is in the Softmax loop at trace index `t`, at the site of pc `pc` of round `i`,
after `R` rescales. -/
def SoftAt (Q : Params) (L : Launch) (X : Execution) (g t pc i R : Nat) : Prop :=
  ∃ w ent d n, Frame.stateAt (thread Q L) X g t = some (some (softState w ent d n)) ∧
    d.site.pc = pc ∧ d.i = i ∧ n (.atPc 2326) = R

private theorem site_999 (s : Site) (h : s.pc = 999) : s = .bar20 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_1009 (s : Site) (h : s.pc = 1009) : s = .tmemSt := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_2260 (s : Site) (h : s.pc = 2260) : s = .ldO := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem flat_not {u e} {p : Event → Bool} (get : X.get (h, u) = some e)
    (hp : p e = false) : ((X.tr h).take (u + 1)).countP p = ((X.tr h).take u).countP p := by
  have : (X.tr h)[u]? = some e := get
  rw [List.take_add_one, this, Option.toList_some, List.countP_append]
  simp [hp]

/-- From the round's rendezvous on: a lane at the mandatory rendezvous (pc 999) of a round has
decided not to rescale (its shuffle skips, at the barrier ordinal of the lane at the O load) or
it has made the store wait (pc 2329) as its last collective event. -/
private theorem from_bar20 {t b i R} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (sw : SameWarp L g h) (hu : NoUbLane X h) (hbt : b ≤ t) (ht : t ≤ (X.tr h).length)
    {j} (nug : Frame.NoUbBefore X g j) (hj : j ≤ (X.tr g).length)
    (sg : SoftAt Q L X g j 2260 i R) (pos : 0 < i)
    (sb : SoftAt Q L X h b 999 i R)
    (hc : ((X.tr h).take b).countP isTcColl = ((X.tr h).take t).countP isTcColl) :
    Lib.Dissent L X g j h t := by
  obtain ⟨w, ent, d, n, hs, hpc, hi, hR⟩ := sb
  obtain ⟨wg, entg, dg, ng, hsg, hpcg, hig, hRg⟩ := sg
  have site : d.site = .bar20 := site_999 _ hpc
  have siteg : dg.site = .ldO := site_2260 _ hpcg
  have hb : b ≤ (X.tr h).length := hbt.trans ht
  obtain ⟨v, old, cnt, ev, rfl, hold, gev, nxt⟩ := soft_prev hb (by rintro rfl; cases site) hs
  have nu := hu.kind gev
  have pce : ev.pc = old.site.pc :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX gev hold nu
  rcases pred_bar20 nxt site with ⟨t1, m1, a1, b1, c1, r1, ok1, kind1, skip1⟩ | t1 | ⟨t1, zero⟩
  · left
    obtain ⟨p, kd⟩ := ev
    have pc2 : p = 2255 := by simpa [t1, Softmax.Site.pc] using pce
    subst pc2
    cases kind1
    obtain ⟨rfl, -, -⟩ := shuffle_2255_shape hp hX gev
    refine ⟨v, a1, b1, c1, r1, ok1, gev, (Control.skip_free L h a1 r1).symm.trans skip1, ?_⟩
    have o1 := data_ordinal hp hX hb hs (hu.before (v + 1))
    have o2 := data_ordinal hp hX hj hsg nug
    have f1 : n (.bar 0) = ((X.tr h).take (v + 1)).countP (Execution.isBarId 0) := by
      simpa [cls_bar0] using fcount hs (.bar 0)
    have f2 : ng (.bar 0) = ((X.tr g).take j).countP (Execution.isBarId 0) := by
      simpa [cls_bar0] using fcount hsg (.bar 0)
    have flat := flat_not (p := Execution.isBarId 0) gev (by simp [Execution.isBarId])
    have cta : h / L.block = g / L.block := sw.1.2.2.symm
    rw [cta] at o1
    simp only [Softmax.fixedCount, Softmax.syncPosition, site, siteg, hi, hig] at o1 o2
    omega
  · right
    obtain ⟨p, kd⟩ := ev
    have pc2 : p = 2329 := by simpa [t1, Softmax.Site.pc] using pce
    subst pc2
    have tc : isTcColl ⟨2329, kd⟩ = true := by
      rw [Lib.tcColl_event hX gev nu]
      simp [Lib.dataPcs]
    have := countP_take_succ (p := isTcColl) gev tc
    exact ⟨v, kd, gev, by omega⟩
  · omega

/-- **A lane after the rescale decision of a round is not at the same events as a lane before
it**: the lane has skipped the rescale (its shuffle, at the barrier ordinal of the lane at the O
load), or it made the store wait as its last collective event. -/
public theorem soft_dissent {t i R pc j} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (sw : SameWarp L g h) (hu : NoUbLane X h) (ht : t ≤ (X.tr h).length)
    (nug : Frame.NoUbBefore X g j) (hj : j ≤ (X.tr g).length)
    (hpc : pc = 999 ∨ pc = 1009) (sh : SoftAt Q L X h t pc i R)
    (sg : SoftAt Q L X g j 2260 i R) (pos : 0 < i) :
    Lib.Dissent L X g j h t := by
  rcases hpc with rfl | rfl
  · exact from_bar20 hp hX sw hu le_rfl ht nug hj sg pos sh rfl
  · obtain ⟨w, ent, d, n, hs, hpc, hi, hR⟩ := sh
    have site : d.site = .tmemSt := site_1009 _ hpc
    obtain ⟨u, old, cnt, ev, rfl, hold, gev, nxt⟩ := soft_prev ht (by rintro rfl; cases site) hs
    obtain ⟨t1, t2⟩ := pred_tmemSt nxt site
    have nu := hu.kind gev
    have pce : ev.pc = 999 := by
      rw [Frame.event_pcU (fun g hg => thread_sound hp hg) hX gev hold nu]
      exact congrArg Softmax.Site.pc t1
    have bz : Execution.isBarId 0 ev = true := by
      rw [Lib.zero_event hX hp.block gev nu, pce]
      decide +kernel
    have tcf : isTcColl ev = false := by
      rw [Lib.tcColl_event hX gev nu]
      obtain ⟨pe, ke⟩ := ev
      cases ke <;> simp_all [Execution.isBarId, isTmemOp, Lib.dataPcs]
    have c1 := flat_not (p := isTcColl) gev tcf
    have c2 := flat_not (p := cls (.atPc 2326)) gev (by simp [cls, pce])
    have f1 : cnt (.atPc 2326) = ((X.tr h).take u).countP (cls (.atPc 2326)) := fcount hold _
    have f2 : n (.atPc 2326) = ((X.tr h).take (u + 1)).countP (cls (.atPc 2326)) := fcount hs _
    refine from_bar20 hp hX sw hu (b := u) (by omega) ht nug hj sg pos
      ⟨_, _, old, cnt, hold, congrArg Softmax.Site.pc t1, by omega, ?_⟩ (by omega)
    omega

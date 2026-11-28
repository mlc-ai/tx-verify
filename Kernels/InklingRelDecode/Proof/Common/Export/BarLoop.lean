-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
public import Kernels.InklingRelDecode.Proof.Lib.PostVisit
import Kernels.InklingRelDecode.Proof.Common.BarCmp
import Kernels.InklingRelDecode.Proof.Common.PreloadOrder
import Kernels.InklingRelDecode.Proof.Common.SoftFixed
import Kernels.InklingRelDecode.Proof.Common.SoftSite
public import Kernels.InklingRelDecode.Proof.Iface.BarRows.Base
public import Kernels.InklingRelDecode.Proof.Common.Export.TcLag
import Kernels.InklingRelDecode.Proof.Softmax.Export.PostVisit
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

/-! # A data lane with no more barrier-0 events is no later than a half-CTA rendezvous

The lane's count of barrier-0 events and its count of optional rendezvous (pc 2326) compare with
the rendezvous lane's (`hV`: the lane's fixed rendezvous are no more). Then its clock is no
later, equal only at the same site, or the lane has just passed the rescale decision of the
round of an optional rendezvous (`Lib.PostVisit`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Sched TcState

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The outcome: the lane `y` at `t` is no later than the lane `g` at its event `j` of pc `pc`,
and equal only at the site of the event with the same fixed count; or, at an optional rendezvous,
it is past the decision of its round. -/
public def LoopLe (Q : Params) (L : Launch) (X : Execution) (g j y t pc : Nat) : Prop :=
  (timeAt (schedule Q L) X y t ≤ timeAt (schedule Q L) X g j ∧
    (timeAt (schedule Q L) X y t = timeAt (schedule Q L) X g j →
      (∀ e, X.get (y, t) = some e → e.pc = pc) ∧
      ((X.tr g).take j).countP (Execution.isBarId 0) +
        ((X.tr y).take t).countP (fun e => e.pc == 2326) =
      ((X.tr y).take t).countP (Execution.isBarId 0) +
        ((X.tr g).take j).countP (fun e => e.pc == 2326))) ∨
  (pc = 2326 ∧ ((X.tr g).take j).countP (Execution.isBarId 0) +
        ((X.tr y).take t).countP (fun e => e.pc == 2326) =
      ((X.tr y).take t).countP (Execution.isBarId 0) +
        ((X.tr g).take j).countP (fun e => e.pc == 2326) ∧ Lib.PostVisit L X y t)

/-- The counts of a followed state, as counts of the prefix. -/
private theorem counts {Q L X y t s} (hs : Frame.stateAt (thread Q L) X y t = some (some s)) :
    s.2 (.bar 0) = ((X.tr y).take t).countP (Execution.isBarId 0) ∧
      s.2 (.atPc 2326) = ((X.tr y).take t).countP (fun e => e.pc == 2326) := by
  refine ⟨?_, fcount hs (.atPc 2326)⟩
  simpa [cls_bar0] using fcount hs (.bar 0)

private theorem soft_ne_epi {Q L g w ent d n} (inv : (thread Q L g).inv (softState w ent d n)) :
    d.site ≠ .epilogue := by
  intro e
  have pl := state_role (Q := Q) (L := L) (g := g) (softState w ent d n)
  have hpc : (thread Q L g).pc (softState w ent d n) = 2565 := by
    change d.site.pc = _
    rw [e]; rfl
  rw [hpc] at pl
  obtain ⟨_, _, _, _, h⟩ := pl.epilogue (by omega) (by omega) inv
  cases h

/-- The comparison of any data lane's state with a Softmax state at a half-CTA rendezvous. -/
private theorem y_vs_soft {j t y w ent dg ng} {s : (thread Q L y).D}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hg : g < L.threads) (hy : y < L.threads) (nug : NoUbBefore X g j) (nuy : NoUbLane X y)
    (cta : y / L.block = g / L.block) (ly : y % L.block < 128) (hj : j ≤ (X.tr g).length)
    (hsg : stateAt (thread Q L) X g j = some (some (softState w ent dg ng)))
    (siteE : dg.site = .bar20 ∨ dg.site = .bar21 ∨ dg.site = .bar22 ∨ dg.site = .bar23 ∨
      dg.site = .bar24)
    (ht : t ≤ (X.tr y).length) (hs : stateAt (thread Q L) X y t = some (some s))
    (hV : ((X.tr y).take t).countP (Execution.isBarId 0) +
        ((X.tr g).take j).countP (fun e => e.pc == 2326) ≤
      ((X.tr g).take j).countP (Execution.isBarId 0) +
        ((X.tr y).take t).countP (fun e => e.pc == 2326)) :
    LoopLe Q L X g j y t dg.site.pc := by
  obtain ⟨cNg, cVg⟩ := counts hsg
  obtain ⟨cNy, cVy⟩ := counts hs
  have tg : timeAt (schedule Q L) X g j = Softmax.time dg := by
    rw [time_at hsg]; exact siteTime_soft
  have g1200 : 1200 ≤ Softmax.time dg := by
    rcases siteE with e | e | e | e | e <;>
      simp [Softmax.time, e, Softmax.Site.position, Lib.Slots.softmax, Lib.Slots.frame,
        Lib.Slots.stride] <;> omega
  have og := data_ordinal hp hX hj hsg nug
  obtain ⟨sh, nh⟩ := s
  change nh (.bar 0) = _ at cNy
  change nh (.atPc 2326) = _ at cVy
  change ng (.bar 0) = _ at cNg
  change ng (.atPc 2326) = _ at cVg
  rcases sh with st | ⟨r, d⟩
  · have s26 := (siteTime_startup (Q := Q) (L := L) (g := y) st nh).1
    left
    rw [time_at hs, tg]
    refine ⟨by omega, fun h => by omega⟩
  · rcases r with r | r
    swap
    · exact (no_stub hp hX ht hs).elim
    cases r with
    | dispatch w x => exact absurd (worker_warp hp hX ht hs).1 (by omega)
    | prologue wy =>
      rcases d with d | ⟨enty, d | ⟨u, d⟩⟩
      · have := siteTime_pro (Q := Q) (L := L) (g := y) (w := wy) (d := d) (n := nh)
        left
        rw [time_at hs, tg]
        refine ⟨by omega, fun h => by omega⟩
      · have oy := data_ordinal hp hX ht hs (nuy.before t)
        rw [cta] at oy
        have tbl := reached_table hf hy (nuy.before t) hs
        have tblg := reached_table hf hg nug hsg
        have ne := soft_ne_epi tbl.1
        have loopg : dg.i < ent.limit := by
          have := tblg.1.1.loop
          rcases siteE with e | e | e | e | e <;> exact this (by simp [e]) (by simp [e])
            (by simp [e]) (by simp [e])
        have lim : ent.limit = enty.limit := by
          rw [reached_limit hp hX hg hj hsg, reached_limit hp hX hy ht hs, cta]
        have bnd := tbl.1.1.bound
        have pos : Softmax.needsPrevious dg.site = true → 0 < dg.i :=
          shfl_previous hp hX hj hsg nug
        obtain ⟨sy, iy, vy⟩ := d
        obtain ⟨sg, ig, vg⟩ := dg
        have fc : Softmax.fixedCount ⟨sy, iy, vy⟩ ≤ Softmax.fixedCount ⟨sg, ig, vg⟩ := by
          omega
        rcases Softmax.soft_bar_cmp (by simpa using siteE) fc (fun h => absurd h ne)
          (by simpa [lim] using loopg) with ⟨l1, l2⟩ | ⟨c1, c2, c3, c4⟩
        · left
          rw [time_at hs, tg]
          refine ⟨l1, fun h => ?_⟩
          obtain ⟨e1, e2⟩ := l2 h
          subst e1; subst e2
          refine ⟨fun e he' => ?_, by simp only [Softmax.fixedCount] at *; omega⟩
          have := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he' hs (nuy.kind he')
          exact this
        · right
          subst c1
          have ipos : 0 < ig := pos (by simp [Softmax.needsPrevious])
          have hpc : Softmax.Site.pc sy = 2328 ∨ Softmax.Site.pc sy = 2329 ∨
              Softmax.Site.pc sy = 999 := by
            rcases c3 with rfl | rfl | rfl <;> simp [Softmax.Site.pc]
          refine ⟨rfl, by omega, ?_⟩
          exact Softmax.Export.post_visit hp hX nuy ht hpc
            ⟨wy, enty, ⟨sy, iy, vy⟩, nh, hs, rfl, rfl, rfl⟩ (c2 ▸ ipos)
      · exfalso
        have oy := epilogue_ordinal hp hX ht hs (nuy.before t)
        rw [cta] at oy
        have tblg := reached_table hf hg nug hsg
        have loopg : dg.i < ent.limit := by
          have := tblg.1.1.loop
          rcases siteE with e | e | e | e | e <;> exact this (by simp [e]) (by simp [e])
            (by simp [e]) (by simp [e])
        have lim : ent.limit = enty.limit := by
          rw [reached_limit hp hX hg hj hsg, reached_limit hp hX hy ht hs, cta]
        have far : Softmax.fixedCount ⟨.epilogue, enty.limit, {}⟩ ≥ 4 * enty.limit := by
          simp [Softmax.fixedCount, Softmax.syncPosition]
        have near : Softmax.fixedCount dg ≤ 4 * dg.i + 3 := by
          obtain ⟨sg, ig, vg⟩ := dg
          rcases siteE with e | e | e | e | e <;> simp only at e <;> subst e <;>
            simp [Softmax.fixedCount, Softmax.syncPosition]
        omega

/-- The comparison of any data lane's state with a prologue state at a rendezvous. -/
private theorem y_vs_pro {j t y w dg ng} {s : (thread Q L y).D}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hy : y < L.threads) (nug : NoUbBefore X g j) (nuy : NoUbLane X y)
    (cta : y / L.block = g / L.block) (ly : y % L.block < 128) (hj : j ≤ (X.tr g).length)
    (hsg : stateAt (thread Q L) X g j = some (some (.inr ⟨.inl (.prologue w), .inl dg⟩, ng)))
    (sync : Prologue.preloadSync dg.site = true)
    (ht : t ≤ (X.tr y).length) (hs : stateAt (thread Q L) X y t = some (some s))
    (hV : ((X.tr y).take t).countP (Execution.isBarId 0) +
        ((X.tr g).take j).countP (fun e => e.pc == 2326) ≤
      ((X.tr g).take j).countP (Execution.isBarId 0) +
        ((X.tr y).take t).countP (fun e => e.pc == 2326)) :
    LoopLe Q L X g j y t dg.site.pc := by
  obtain ⟨cNg, cVg⟩ := counts hsg
  obtain ⟨cNy, cVy⟩ := counts hs
  have pg := preload_ordinal hp hX hj hsg nug
  have clg := preload_clear hp hX hj hsg nug
  have tg : timeAt (schedule Q L) X g j = 100 + Prologue.allSites.idxOf dg.site := by
    rw [time_at hsg]; exact siteTime_pro_idx
  have gateg := pro_gate hp hX hg hj hsg nug
  have posg := pro_pos_le (preload_le_three Q L (g / L.block)) gateg sync
  obtain ⟨sh, nh⟩ := s
  change nh (.bar 0) = _ at cNy
  change nh (.atPc 2326) = _ at cVy
  change ng (.bar 0) = _ at cNg
  change ng (.atPc 2326) = _ at cVg
  rcases sh with st | ⟨r, d⟩
  · have s26 := (siteTime_startup (Q := Q) (L := L) (g := y) st nh).1
    left
    rw [time_at hs, tg]
    refine ⟨by omega, fun h => by omega⟩
  · rcases r with r | r
    swap
    · exact (no_stub hp hX ht hs).elim
    cases r with
    | dispatch w x => exact absurd (worker_warp hp hX ht hs).1 (by omega)
    | prologue wy =>
      rcases d with d | ⟨enty, d | ⟨u, d⟩⟩
      · have py := preload_ordinal hp hX ht hs (nuy.before t)
        have cly := preload_clear hp hX ht hs (nuy.before t)
        have gatey := pro_gate hp hX hy ht hs (nuy.before t)
        rw [cta] at gatey
        obtain ⟨c1, c2⟩ := pro_cmp (preload_le_three Q L (g / L.block)) gateg gatey sync (by
          rw [cta] at py; omega)
        left
        rw [time_at hs, tg, siteTime_pro_idx]
        refine ⟨by omega, fun h => ?_⟩
        have same := c2 (by omega)
        refine ⟨fun e he' => ?_, by rw [cta] at py; rw [same] at py; omega⟩
        have := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he' hs (nuy.kind he')
        rw [this]; exact congrArg Prologue.Site.pc same
      · exfalso
        have oy := data_ordinal hp hX ht hs (nuy.before t)
        have fx := soft_fixed_total hp hX ht hs (nuy.before t)
        rw [cta] at oy
        have clg' : ng (.atPc 2326) = 0 := clg
        omega
      · exfalso
        have oy := epilogue_ordinal hp hX ht hs (nuy.before t)
        rw [cta] at oy
        have far : Softmax.fixedCount ⟨.epilogue, enty.limit, {}⟩ ≥ 2 := by
          simp only [Softmax.fixedCount, Softmax.syncPosition]
          split <;> omega
        have clg' : ng (.atPc 2326) = 0 := clg
        omega

private theorem soft_bar_site (s : Softmax.Site) (h : s.pc ∈ BarRow.halfZeroSites)
    (hi : 574 < s.pc) : s = .bar20 ∨ s = .bar21 ∨ s = .bar22 ∨ s = .bar23 ∨ s = .bar24 := by
  revert h hi
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **A data lane with no more fixed rendezvous than a half-CTA rendezvous is no later than it.**
The lane `y` at `t` has made no more barrier-zero events than the lane `g` before its event `j`,
counting the optional rendezvous aside (`hV`). -/
public theorem loop_cmp {j t y pc cnt md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hy : y < L.threads)
    (nuy : NoUbLane X y) (cta : y / L.block = g / L.block) (ly : y % L.block < 128)
    (he : X.get (g, j) = some ⟨pc, .bar 0 cnt md⟩) (hh : pc ∈ BarRow.halfZeroSites)
    (ht : t ≤ (X.tr y).length) (hal : TcAlive Q L X y t)
    (hV : ((X.tr y).take t).countP (Execution.isBarId 0) +
        ((X.tr g).take j).countP (fun e => e.pc == 2326) ≤
      ((X.tr g).take j).countP (Execution.isBarId 0) +
        ((X.tr y).take t).countP (fun e => e.pc == 2326)) :
    LoopLe Q L X g j y t pc := by
  have hg := Frame.lt_of_get hX he
  have nug := Frame.noUbBefore_of_get hX he
  have hj := (List.getElem?_eq_some_iff.mp he).1.le
  have clean : ∀ f, (⟨pc, .bar 0 cnt md⟩ : Event).kind ≠ .ub f := by simp
  have hh' := hh
  simp only [BarRow.halfZeroSites, List.mem_cons, List.not_mem_nil, or_false] at hh'
  obtain ⟨s, hs⟩ := alive_iff.1 hal
  by_cases pro : pc < 574
  · obtain ⟨st, hst, -⟩ := Frame.good_stateU (J := fun _ _ => True)
      (fun g hg => thread_sound hp hg) hX he (fun _ f eq => clean f (congrArg Event.kind eq))
      ⟨control_tracked hp hX g j hg, fun _ _ => trivial⟩
    have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hst clean
    change pc = _ at pos
    obtain ⟨w, d, n, rfl⟩ := (pos ▸ state_role st).prologue (by omega) pro
    change pc = d.site.pc at pos
    subst pos
    exact y_vs_pro hp hX hg hy nug nuy cta ly hj hst (sync_of_half hh) ht hs hV
  · obtain ⟨w, ent, d, n, hst, pc'⟩ :=
      at_site hp hX he clean (show 574 < pc by omega) (show pc < 2331 by omega)
    have pc2 : pc = d.site.pc := pc'
    have gt : 574 < d.site.pc := by omega
    have site := soft_bar_site d.site (pc2 ▸ hh) gt
    subst pc2
    exact y_vs_soft hp hX hf hg hy nug nuy cta ly hj hst site ht hs hV

end PTX.Kernels.InklingRelDecode.Proof.Export

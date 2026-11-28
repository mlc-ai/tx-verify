-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Softmax.Export.TcLag
import Kernels.InklingRelDecode.Proof.Softmax.Export.Dissent
public import Kernels.InklingRelDecode.Proof.Lib.Dissent
import Kernels.InklingRelDecode.Proof.Startup.Export.SiteCount
import Kernels.InklingRelDecode.Proof.Common.ResourceCount
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
public import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof PTX.Sched PTX.Tmem.Pair TcState
variable {Q : Params} {L : Launch} {g : Nat}
private theorem start_coll {m X h t e} {st : Startup.D} {nh : Cls → Nat} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hu : NoUbLane X h)
    (he : X.get (h, t) = some e) (hs : Frame.stateAt (thread Q L) X h t = some (some (.inl st, nh)))
    (hnc : isTcColl e = false) : st.site ≠ .alloc ∧ st.site ≠ .relinq := by
  have ev := start_ev hp hX he hs (fun f hk => hu.kind he f hk)
  obtain ⟨site, tm, x, w⟩ := st
  constructor <;> intro hsite <;> simp only at hsite <;> subst hsite <;>
    simp only [Startup.Ev] at ev <;>
    subst ev <;> simp [isTcColl] at hnc
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
private theorem site_pc_off {m X h t e} {s : (thread Q L h).D} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hu : NoUbLane X h)
    (he : X.get (h, t) = some e) (hs : Frame.stateAt (thread Q L) X h t = some (some s))
    (hnc : isTcColl e = false) :
    e.pc = (thread Q L h).pc s ∧ e.pc ∉ Lib.dataPcs ∧ isTmemOp e = false := by
  have nu := hu.kind he
  have := Lib.tcColl_event hX he nu
  rw [hnc] at this
  simp only [Bool.false_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
  exact ⟨Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs nu, this.2, this.1⟩
/-- The lane's machine state at index `t` is alive. -/
public def TcAlive (Q : Params) (L : Launch) (X : Execution) (h t : Nat) : Prop :=
  ∃ d, Frame.stateAt (schedule Q L).code X h t = some (some d)
/-- A lane's clock at `t` is its alive state's, one more than before the stopping event, or 0. -/
public theorem tc_time_cases {X : Execution} (hf : Follow Q L X) {h : Nat} (hh : h < L.threads)
    (t : Nat) : TcAlive Q L X h t ∨ timeAt (schedule Q L) X h t = 0 ∨
      (0 < t ∧ TcAlive Q L X h (t - 1) ∧
        timeAt (schedule Q L) X h t = timeAt (schedule Q L) X h (t - 1) + 1) := by
  rcases h1 : Frame.stateAt (thread Q L) X h t with _ | _ | d
  · rcases t with _ | t
    · simp [Frame.stateAt_zero] at h1
    rcases h0 : Frame.stateAt (thread Q L) X h t with _ | _ | d0
    · exact .inr (.inl (time_zero h0 h1))
    · exact absurd h0 (tracked_ne hf hh t)
    · exact .inr (.inr ⟨by omega, alive_iff.2 ⟨d0, h0⟩,
        by simp only [Nat.add_sub_cancel]; rw [time_dead h0 h1, time_at h0]⟩)
  · exact absurd h1 (tracked_ne hf hh t)
  · exact .inl (alive_iff.2 ⟨d, h1⟩)
/-- **A lane with the collective events of a lane at a collective event is no later** (strictly so
when its event at `t` is not collective), unless it decided the rescale the other way. -/
public theorem tc_lag_at {m X j t pc k h} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hu : NoUbLane X h)
    (hg : g < L.threads) (hh : h < L.threads) (sw : SameWarp L g h)
    (he : X.get (g, j) = some ⟨pc, k⟩) (tc : isTcColl ⟨pc, k⟩ = true)
    (ht : t ≤ (X.tr h).length) (hal : TcAlive Q L X h t)
    (hv : ∀ P ∈ Lib.dataPcs, ((X.tr h).take t).countP (fun e => e.pc == P) =
      ((X.tr g).take j).countP (fun e => e.pc == P))
    (htm : tmemOps ((X.tr h).take t) = tmemOps ((X.tr g).take j)) :
    (timeAt (schedule Q L) X h t ≤ timeAt (schedule Q L) X g j ∧ (∀ e, X.get (h, t) = some e →
      isTcColl e = false → timeAt (schedule Q L) X h t < timeAt (schedule Q L) X g j)) ∨
      (pc = 2260 ∧ Lib.Dissent L X g j h t) := by
  obtain ⟨s, hs⟩ := alive_iff.1 hal
  rw [time_at hs]
  have hk' := (List.getElem?_eq_some_iff.mp he).1.le
  have cta : g / L.block = h / L.block := sw.1.2.2
  have lg : g % L.block < 128 := Export.tc_data_lane hp hX hf he tc
  have lh : h % L.block < 128 := by have := sw.2; omega
  have nubh := hu.before t
  obtain ⟨sE, hsE, tiE, invE, nubE, cls⟩ := coll_state hp hX hf he tc
  obtain ⟨tm1, tm2, tm3, tm4⟩ := Export.tc_tmem hp hX hf he tc
  have tbl := reached_table hf hh nubh hs
  have ti := tc_inv hp hX hf hh ht hs nubh
  have vecn : ∀ P ∈ Lib.dataPcs, s.2 (.atPc P) = sE.2 (.atPc P) := fun P hP =>
    (fcount hs (.atPc P)).trans ((hv P hP).trans (fcount hsE (.atPc P)).symm)
  rw [time_at hsE]
  obtain ⟨sh, nh⟩ := s
  rcases sh with st | ⟨r, d⟩
  · have s26 := (siteTime_startup (Q := Q) (L := L) (g := h) st nh).1
    have e26 := siteTime_startup_early (Q := Q) (L := L) (g := h) st nh
    left
    rcases cls with ⟨st0, n0, rfl, hpc0, hpc2⟩ | ⟨w0, ent0, dE, nE, rfl, hpcE, hlE⟩ |
        ⟨w0, ent0, dE, nE, rfl, hpcE, hlE⟩
    · have lowh : h % L.block < 32 := by have := sw.2; have := tm1 (by omega); omega
      have rp := resource_prefix hp hX hf hh lowh ht nubh hs
      change tmemOps _ = Startup.resourceCount (h % L.block) st.site at rp
      have pcs := siteTime_startup_pc (Q := Q) (L := L) (g := g) st0 n0
      rw [← hpc0] at pcs
      rcases hpc2 with h11 | h11
      · have z : Startup.resourceCount (h % L.block) st.site = 0 := by
          rw [← rp, htm]; exact tm2 h11
        have al := Startup.Export.site_no_ops lowh z
        have := e26.1 al
        have := (pcs.1 h11).1
        refine ⟨by omega, fun e he' hnc => ?_⟩
        exact absurd al (start_coll hp hX hu he' hs hnc).1
      · have z : Startup.resourceCount (h % L.block) st.site = 1 := by
          rw [← rp, htm]; exact tm3 h11
        obtain ⟨n1, n2, n3⟩ := Startup.Export.site_one_op lowh z
        have := pcs.2 h11
        by_cases hr : st.site = .relinq
        · exact ⟨by rw [e26.2.1 hr]; omega, fun e he' hnc =>
            absurd hr (start_coll hp hX hu he' hs hnc).2⟩
        · have := e26.2.2 n1 hr n2 n3
          exact ⟨by omega, fun _ _ _ => by omega⟩
    · have := Softmax.Export.time_coll (hpcE ▸ hlE)
      rw [siteTime_soft]
      exact ⟨by omega, fun _ _ _ => by omega⟩
    · have := Epilogue.Export.time_fin dE
      rw [siteTime_epi]
      exact ⟨by omega, fun _ _ _ => by omega⟩
  · rcases r with r | r
    swap
    · exact (no_stub hp hX ht hs).elim
    cases r with
    | dispatch w x => exact absurd (worker_warp hp hX ht hs).1 (by omega)
    | prologue w =>
      have notStart : ¬ ∃ st n, sE = (.inl st, n) ∧ pc = st.site.pc ∧ (pc = 11 ∨ pc = 15) := by
        rintro ⟨st0, n0, rfl, hpc0, hpc2⟩
        have lowh : h % L.block < 32 := by have := sw.2; have := tm1 (by omega); omega
        have rp := resource_prefix hp hX hf hh lowh ht nubh hs
        simp only [resourcePhase] at rp
        rcases hpc2 with h11 | h11
        · have := tm2 h11; omega
        · have := tm3 h11; omega
      rcases cls with h1 | ⟨w0, ent0, dE, nE, rfl, hpcE, hlE⟩ | ⟨w0, ent0, dE, nE, rfl, hpcE, hlE⟩
      · exact absurd h1 notStart
      · have late := Softmax.Export.time_coll (hpcE ▸ hlE)
        rw [siteTime_soft]
        rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
        · have := siteTime_pro (Q := Q) (L := L) (g := h) (w := w) (d := d) (n := nh)
          exact .inl ⟨by omega, fun _ _ _ => by omega⟩
        · have vI := ti
          obtain ⟨cI, vI⟩ := ti
          obtain ⟨cE, vE⟩ := tiE
          have ep := soft_ne_epi tbl.1
          have prevE := shfl_previous hp hX hk' hsE nubE
          rcases Softmax.Export.soft_lag (R := nh (.atPc 2326)) (RE := nE (.atPc 2326))
            (hpcE ▸ hlE) (fun P hP => by rw [← cI P hP, ← cE P hP]; exact vecn P hP) vI vE prevE
            ep with ⟨l1, l2⟩ | ⟨c1, c2, c3, c4⟩
          · rw [siteTime_soft]
            refine .inl ⟨l1, fun e he' hnc => l2 ?_⟩
            obtain ⟨p1, p2, -⟩ := site_pc_off hp hX hu he' hs hnc
            intro hl
            apply p2
            change e.pc = _ at p1
            rw [p1]
            simp only [Lib.loopTcPcs, Lib.dataPcs, List.mem_cons, List.not_mem_nil, or_false]
              at hl ⊢
            omega
          · have pos : 0 < dE.i := prevE (by simp [Softmax.needsPrevious, c1])
            refine .inr ⟨by rw [hpcE, c1]; rfl, Softmax.Export.soft_dissent (pc := d.site.pc) hp hX
              sw hu ht nubE hk' (by rcases c2 with s | s <;> simp [s, Softmax.Site.pc])
              ⟨_, _, d, _, hs, rfl, rfl, rfl⟩
              ⟨_, _, dE, _, hsE, by rw [c1]; rfl, c3.symm, c4.symm⟩ (c3 ▸ pos)⟩
        · exfalso
          obtain ⟨cI, -⟩ := ti
          obtain ⟨cE, -⟩ := tiE
          have a := cI 1010 (by simp [Lib.dataPcs])
          have b := cE 1010 (by simp [Lib.dataPcs])
          have c := vecn 1010 (by simp [Lib.dataPcs])
          have l1 := reached_limit hp hX hg hk' hsE
          have l2 := reached_limit hp hX hh ht hs
          have lt := Softmax.Export.coll_i_lt invE.1 (hpcE ▸ hlE)
          simp [Softmax.softCount, Epilogue.epiCount, Softmax.afterTmemWait] at a
          rw [Softmax.Export.count_1010 _ (hpcE ▸ hlE)] at b
          rw [cta] at l1
          change nh (.atPc 1010) = nE (.atPc 1010) at c
          omega
      · have fin := Epilogue.Export.time_fin dE
        rw [siteTime_epi]
        rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
        · have := siteTime_pro (Q := Q) (L := L) (g := h) (w := w) (d := d) (n := nh)
          exact .inl ⟨by omega, fun _ _ _ => by omega⟩
        · have lf := (Softmax.Export.time_le_finish tbl.1.1).2 (soft_ne_epi tbl.1)
          rw [siteTime_soft]
          exact .inl ⟨by omega, fun _ _ _ => by omega⟩
        · obtain ⟨cI, liveH⟩ := ti
          obtain ⟨cE, liveE⟩ := tiE
          have l1 := reached_loop hp hX hg hk' hsE
          have l2 := reached_loop hp hX hh ht hs
          have lim : ent0.limit = ent.limit := by rw [l1.1, l2.1, cta]
          have sk : (epiEntry ent (h % L.block)).skip = (epiEntry ent0 (g % L.block)).skip := by
            have a : (epiEntry ent (h % L.block)).skip = decide (ent.limit = 0) := l2.2
            have b : (epiEntry ent0 (g % L.block)).skip = decide (ent0.limit = 0) := l1.2
            rw [a, b, lim]
          have hE : dE.site = .load ∨ dE.site = .waitLd ∨ dE.site = .dealloc := by
            obtain ⟨sE', vE'⟩ := dE
            cases sE' <;> simp [Epilogue.Site.pc, Epilogue.storePc] at hpcE hlE ⊢ <;> omega
          have vc (P : Nat) (hP : P = 2607 ∨ P = 2608) :
              Epilogue.epiCount (epiEntry ent (h % L.block)).skip d.site P =
                Epilogue.epiCount (epiEntry ent (h % L.block)).skip dE.site P := by
            have hP' : P ∈ Lib.dataPcs := by simp only [Lib.dataPcs]; simp; omega
            have a := cI P hP'
            have b := cE P hP'
            have c := vecn P hP'
            change nh (.atPc P) = nE (.atPc P) at c
            rw [← sk] at b
            have z (l r : Nat) : Softmax.softCount .epilogue l r P = 0 := by
              rcases hP with rfl | rfl <;> simp [Softmax.softCount]
            have := z ent.limit (nh (.atPc 2326))
            have := z ent0.limit (nE (.atPc 2326))
            omega
          have nex : d.site = .exit → dE.site ≠ .dealloc := by
            intro hx hd
            have p2851 : pc = 2851 := by rw [hpcE, hd]; rfl
            have lowg : g % L.block / 32 = 0 := tm1 (by omega)
            have lowh : h % L.block < 32 := by have := sw.2; omega
            have rp := resource_prefix hp hX hf hh lowh ht nubh hs
            have o2 := tm4 (by omega) (by omega)
            simp [resourcePhase, dataEnd, softEnd, hx, Epilogue.Site.pc, lowg] at rp o2
            omega
          obtain ⟨l1', l2'⟩ := Epilogue.Export.epi_lag hE (vc 2607 (.inl rfl)) (vc 2608 (.inr rfl))
            liveH (fun h' => sk.trans (liveE h')) nex
          rw [siteTime_epi]
          refine .inl ⟨l1', fun e he' hnc => l2' ?_⟩
          obtain ⟨p1, p2, p3⟩ := site_pc_off hp hX hu he' hs hnc
          have dr := data_resource hp hX he' (hu.kind he') hs
          rw [p3] at dr
          change e.pc = d.site.pc at p1
          simp only [Lib.dataPcs, List.mem_cons, List.not_mem_nil, or_false] at p2
          change false = decide (d.site.pc = 2851) at dr
          simp at dr
          omega
end PTX.Kernels.InklingRelDecode.Proof.Export

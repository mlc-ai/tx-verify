-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.TcState
public import Kernels.InklingRelDecode.Proof.Iface.BarRows.Base
import Kernels.InklingRelDecode.Proof.Prologue.Export.RegBand
import Kernels.InklingRelDecode.Proof.Prologue.Export.TimeNext
import Kernels.InklingRelDecode.Proof.Common.BarCmp
import all Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # The clock rises after a barrier-0 event

At a half-CTA or full rendezvous of barrier 0 the state's clock is below its successor's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.TcState
open PTX PTX.Flow PTX.Proof PTX.Sched
variable {Q : Params} {L : Launch} {g : Nat}

theorem start_after {st n ev s1} (step : (thread Q L g).next (.inl st, n) ev = some (some s1))
    (hpc : st.site.pc = 12 ∨ st.site.pc = 14) :
    siteTime (Q := Q) (L := L) (g := g) (.inl st, n) < siteTime s1 := by
  obtain ⟨s1, cnt⟩ := s1
  rw [next_start] at step
  rcases hsu : Startup.succ L g st ev with _ | _ | st' <;> rw [hsu] at step <;>
    simp only [Option.map_some, Option.map_none, reduceCtorEq, Option.some.injEq] at step
  have hx : Startup.enterOf st' = none := by
    obtain ⟨sit, tm, x, w⟩ := st
    cases sit <;> simp [Startup.Site.pc] at hpc <;> simp [Startup.succ] at hsu <;>
      (subst hsu; first | rfl | (split_ifs <;> rfl))
  rw [enter_inl hx] at step
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj step
  exact siteTime_startup_succ _ _ (.inr (.inr hpc)) hsu

private theorem enter_time {w : Value} (d : Prologue.Control.D) (n : Cls → Nat) :
    Prologue.time d ≤ siteTime (Q := Q) (L := L) (g := g)
      (.inr ⟨.inl (.prologue w), (Prologue.Control.checkedCode Q L g w).enter
        (fun e => softCode e L g) (dataExit Q L g w) d⟩, n) := by
  by_cases hx : d.site = .exit
  · rw [Code.enter_some (show dataExit Q L g w d = some (dataEntry Q L g w d) by
      simp [dataExit, hx])]
    have : siteTime (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.prologue w),
        .inr ⟨dataEntry Q L g w d, (softCode (dataEntry Q L g w d) L g).init⟩⟩, n) = 285 := rfl
    rw [this]
    have := (Prologue.Export.regBand d).1
    omega
  · rw [Code.enter_none (show dataExit Q L g w d = none by simp [dataExit, hx])]
    exact Nat.le_refl _

theorem pro_after {w d n ev s1}
    (step : (thread Q L g).next (proState w d n) ev = some (some s1)) :
    siteTime (Q := Q) (L := L) (g := g) (proState w d n) < siteTime s1 := by
  obtain ⟨s1, cnt⟩ := s1
  obtain ⟨p1, m1, rfl⟩ := Code.glue_inr_some (Code.counted_next_some step).1
  obtain ⟨dn, m2, rfl⟩ := Code.glue_inl_some m1
  have lt := Prologue.Export.time_next (Q := Q) (L := L) (g := g) m2
  exact lt.trans_le (enter_time dn cnt)

theorem exit_after {w x d n ev s1} (h : d.site = .exitSync)
    (step : (thread Q L g).next (.inr ⟨.inl (.dispatch w x), .inl d⟩, n) ev = some (some s1)) :
    siteTime (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.dispatch w x), .inl d⟩, n) <
      siteTime s1 := by
  obtain ⟨s1, cnt⟩ := s1
  obtain ⟨p1, m1, rfl⟩ := Code.glue_inr_some (Code.counted_next_some step).1
  change (Dispatch.next L g d ev).map _ = _ at m1
  obtain ⟨site, round⟩ := d
  simp only at h
  subst h
  simp only [Dispatch.next, Option.map_some] at m1
  split_ifs at m1 <;> simp only [Option.some.injEq] at m1 <;> subst m1 <;>
    rw [Code.enter_none (by rfl)] <;>
    simp [siteTime, siteClock, workerClock, dispatchClock]

private theorem start_ne (s : Startup.Site) : s.pc ≠ 2853 := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem loader_ne (s : Loader.Site) : s.pc ≠ 2853 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_ne (s : Mma.Site) : s.pc ≠ 2853 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_ne (s : Epilogue.Site) : s.pc ≠ 2853 := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

private theorem exit_site (s : Dispatch.Site) (h : s.pc = 2853) : s = .exitSync := by
  cases s <;> first | rfl | (exfalso; revert h; decide)

/-- **The clock rises after a rendezvous of barrier 0.** -/
theorem zero_after {s s1 : (thread Q L g).D} {ev} (tab : tableInv Q L g s)
    (step : (thread Q L g).next s ev = some (some s1))
    (site : (thread Q L g).pc s ∈ BarRow.fullZeroSites ++ BarRow.halfZeroSites) :
    siteTime s < siteTime s1 := by
  have pl := state_role s
  generalize e : (thread Q L g).pc s = P at pl site
  simp only [BarRow.fullZeroSites, BarRow.halfZeroSites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at site
  have hr : P < 27 ∨ (27 < P ∧ P < 574) ∨ (574 < P ∧ P < 2331) ∨ P = 2850 ∨ P = 2853 := by
    omega
  rcases hr with h | h | h | h | h
  · obtain ⟨st, n, rfl⟩ := pl.startup h
    exact start_after step (by change st.site.pc = P at e; omega)
  · obtain ⟨w, d, n, rfl⟩ := pl.prologue h.1 h.2
    exact pro_after step
  · obtain ⟨w, ent, d, n, rfl⟩ := pl.softmax h.1 h.2
    refine (soft_fwd tab.1.1 step).2.2 (.inr ?_)
    change d.site.pc = P at e
    simp only [Lib.loopBarPcs, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · obtain ⟨w, ent, d, n, rfl⟩ := pl.epilogue (by omega) (by omega) tab.1
    refine (epi_fwd step).2.2 ?_
    change d.site.pc = P at e
    omega
  · obtain ⟨s0, n⟩ := s
    rcases s0 with st | ⟨r, d⟩
    · exact absurd (e.trans h) (start_ne st.site)
    rcases r with r | r
    swap
    · have e' : (thread Q L g).pc (Sum.inr ⟨Sum.inr r, d⟩, n) = Startup.Entry.pc r := rfl
      rw [e'] at e
      subst h
      exfalso
      revert e
      cases r <;> decide
    cases r with
    | prologue w =>
      rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
      · have := Prologue.Site.pc_range d.site
        change d.site.pc = P at e
        omega
      · change d.site.pc = P at e
        rcases Softmax.Site.pc_range d.site with r | r
        · omega
        · rw [r] at e
          subst h
          exact absurd e (by decide)
      · exact absurd (e.trans h) (epi_ne d.site)
    | dispatch w x =>
      rcases d with d | ⟨i, d⟩
      · exact exit_after (exit_site _ (e.trans h)) step
      · cases i with
        | loader r0 => exact absurd (e.trans h) (loader_ne d.site)
        | mma r0 => exact absurd (e.trans h) (mma_ne d.site)

end PTX.Kernels.InklingRelDecode.Proof.TcState

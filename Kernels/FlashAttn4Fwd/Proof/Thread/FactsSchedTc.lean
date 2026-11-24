-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedSoftTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSchedTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.Tracked

@[expose] public section

/-! # The warp-collective `tcgen05` schedule of every warp (`Cross.TcSched`)

The schedule of a warp is its role's (the role is a function of the warp index):

* the softmax warps (`< 8`): fourteen events per tile (`Soft.tcS`), from the softmax count
  (`Softmax.tcColl_sched`);
* the correction warps (`8 … 11`): their loads and stores of a rescale follow the trip's ballot,
  so their count is not a function of the state alone; their schedule is the premise
  `CorrTcSched`;
* the MMA warp (`12`): its warp-collective `tcgen05` events are its paired Tensor Memory
  operations (no site of the warp loads or stores Tensor Memory), on the schedule `tmemS`;
* the store, loader and idle warps (`13 … 15`) make none: the schedule `noneS` is in the tail,
  after each of their states (`none_time`).

The prologue makes none, before every role's schedule. The four schedules join into one
(`Sched.collSched_union`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The items of the cluster of CTA `c`. -/
abbrev Tc (L : Launch) (c : Nat) : Nat := Tk L (L.clusterOfCta c)

theorem prologue_not_tc {es : List Event} (h : ∀ x ∈ es, Prologue.ProKind x.kind) :
    es.countP isTcColl = 0 := by
  refine List.countP_eq_zero.mpr fun x hx => ?_
  have := h x hx
  obtain ⟨pc, k⟩ := x
  cases k <;> simp_all [Prologue.ProKind, isTcColl]

theorem prologue_tcKind (p : Prologue.D) : tcKind (nextKind (.inl p)) = false := by
  obtain ⟨s⟩ := p
  cases s <;> simp [nextKind, prologueKind, tcKind]

/-! ### The warps without `tcgen05` collectives -/

/-- The schedule of a warp without warp-collective `tcgen05` events: in the tail. -/
def noneS (n T k : Nat) : Nat := tailTime n T (4000 + k)

/-- Every loader state is before the tail's offset 100. -/
theorem Loader.time_lt {g : Nat} {d : Loader.D} (hi : Loader.Inv L g d) :
    loader (Work.n L) (Work.T L g) d < tailTime (Work.n L) (Work.T L g) 100 := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  have hitem := hi.item
  have htrip := hi.trip
  simp only at hitem htrip
  have huse : ∀ (u : Loader.UseK) (o : Nat), o < 16 → (Loader.Site.inItem site = true) →
      (u = .k ∨ u = .v → Loader.Site.inTrip site = true) →
      loaderUse (Work.n L) i (loaderSlot t u) (loaderBand u) o <
        tailTime (Work.n L) (Work.T L g) 100 := by
    intro u o ho hin htr
    have hiT := hitem hin
    unfold loaderUse
    refine Progress.Time.lt_tail ?_ hiT ?_
    · cases u <;> simp only [loaderSlot] <;> first | omega |
        (have := htrip (htr (by simp)); omega)
    · cases u <;> simp only [loaderBand, bandL, span] <;> omega
  cases site with
  | setMaxReg => simp only [loader]; exact Progress.Time.fixed_lt (by decide)
  | head =>
    exact huse .k0 0 (by decide) rfl (by simp)
  | wait u => exact huse u 1 (by decide) rfl (by rintro (rfl | rfl) <;> rfl)
  | elA u => exact huse u 2 (by decide) rfl (by rintro (rfl | rfl) <;> rfl)
  | arrive u => exact huse u 3 (by decide) rfl (by rintro (rfl | rfl) <;> rfl)
  | elC u j =>
    exact huse u (4 + 2 * j.val) (by omega) rfl (by rintro (rfl | rfl) <;> rfl)
  | copy u j =>
    exact huse u (5 + 2 * j.val) (by omega) rfl (by rintro (rfl | rfl) <;> rfl)
  | drain k => simp only [loader]; exact Progress.Time.tail_lt (by omega)
  | drainQ | elTail | arriveTail | exit => exact Progress.Time.tail_lt (by decide)

/-- Every store state is before the tail's offset 2100. -/
theorem Store.time_lt {g : Nat} {d : Store.D} (hi : d.site = .setMaxReg ∨ Store.Inv L g d) :
    store (Work.n L) (Work.T L g) d < tailTime (Work.n L) (Work.T L g) 2100 := by
  obtain ⟨site, i⟩ := d
  cases site with
  | exit => exact Progress.Time.tail_lt (by decide)
  | setMaxReg => simp only [store]; exact Progress.Time.fixed_lt (by decide)
  | _ =>
    have hiT : i < Work.T L g := by
      rcases hi with h | h
      · simp at h
      · exact h (by simp)
    simp only [store, storeAt]
    refine Progress.Time.lt_tail le_rfl hiT ?_
    simp only [bandST, span]
    omega

/-- Every idle state is before every slot. -/
theorem Idle.time_lt (s : Idle.Site) {n T o : Nat} : idle s < tailTime n T o := by
  cases s <;> exact Progress.Time.fixed_lt (by decide)

theorem Soft.tcS_ge (n T st k : Nat) : base ≤ Soft.tcS n T st k := by
  unfold Soft.tcS
  split_ifs
  · omega
  · exact Progress.Time.base_le

theorem mma_tcKind (s : Mma.Site) : tcKind (mmaKind s) = (mmaKind s == .tmem) := by
  cases s <;> rfl

/-- The premise of the correction warps' schedule (owner: the correction package): their loads
and stores of a trip's rescale are made only when the trip's ballot is not zero, so the time of
their `n`-th warp-collective `tcgen05` event is a function of the warp's ballots. -/
def CorrTcSched (L : Launch) (X : Execution) : Prop :=
  ∃ S, Sched.CollSched (timed L) X isTcColl (warpKey L) (fun g => 8 ≤ warpOf L g ∧
      warpOf L g < 12) S

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- The warp-collective `tcgen05` events of a state's thread before it. -/
def tcCnt (L : Launch) : ThreadD → Nat
  | .inr (.softmax s) => 14 * Work.n L * s.i + Soft.tcPos L s
  | .inr (.mma m) => Mma.tmemA m.site
  | _ => 0

/-- **The softmax warps' schedule.** -/
theorem softTcSched (hsc : Soft.SoftTcCount L) :
    Sched.CollSched (timed L) X isTcColl (warpKey L) (fun g => warpOf L g < 8)
      (fun c k => Soft.tcS (Work.n L) (Tc L c.1) (c.2 / 4) k) := by
  refine Sched.collSched_of (fun _ d => tcCnt L d) (fun _ d => tcKind (nextKind d)) ?_ ?_ ?_
    (fun c k => Soft.tcS_mono _ _ _ k)
  · intro g k d hg hG hk hσ
    obtain ⟨hJ, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
        ⟨-, s, rfl⟩ | ⟨hw', hw'', -⟩
    · exact prologue_not_tc hJ.1
    all_goals (try omega)
    exact hsc hJ hinv
  · intro g k d e hg _ hσ he
    exact (fired_kind hpre hX hok hg hσ he).2.1
  · intro g k d hg hG hk hσ
    obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
        ⟨-, s, rfl⟩ | ⟨hw', hw'', -⟩
    · rw [prologue_tcKind p]
      refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      have := Progress.Time.prologue_lt_reg p.site
      have := Soft.tcS_ge (Work.n L) (Tc L (ctaOf L g)) (warpOf L g / 4) 0
      simp only [stateTime, tcCnt, warpKey]
      simp only [regT, base] at *
      omega
    all_goals (try omega)
    have hn : 0 < Work.n L := Mma.trips_pos hpre
    exact Soft.tc_time hn hinv (st := warpOf L g / 4) (by omega)

/-- **The MMA warp's schedule**: its warp-collective `tcgen05` events are its paired Tensor
Memory operations. -/
theorem mmaTcSched :
    Sched.CollSched (timed L) X isTcColl (warpKey L) (fun g => warpOf L g = 12)
      (fun c k => tmemS (Work.n L) (Tc L c.1) k) := by
  refine Sched.collSched_of (fun _ d => tmemCnt d) (fun _ d => tcKind (nextKind d)) ?_ ?_ ?_
    (fun c k => tmemS_mono _ _ k)
  · intro g k d hg hG hk hσ
    obtain ⟨hJ, -, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    have hcongr : ((X.tr g).take k).countP isTcColl =
        ((X.tr g).take k).countP Tmem.Pair.isTmemOp := by
      refine Sched.countP_take_congr ht hg hσ fun {j d' e} hj hσ' he => ?_
      have hk' := fired_kind hpre hX hok hg hσ' he
      rw [hk'.2.1, hk'.2.2.1]
      obtain ⟨-, -, hw'⟩ := state_facts hpre hX ht hok hg (by omega) hσ'
      rcases role_cases hw' with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨-, m, rfl⟩ | ⟨hw', -⟩ |
          ⟨hw', -⟩ | ⟨hw', hw'', -⟩
      · rw [prologue_tcKind p]
        obtain ⟨s⟩ := p
        cases s <;> rfl
      all_goals (try omega)
      exact mma_tcKind m.site
    rw [hcongr]
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨-, m, rfl⟩ | ⟨hw', -⟩ |
        ⟨hw', -⟩ | ⟨hw', hw'', -⟩
    · exact prologue_not_tmem hJ.1
    all_goals (try omega)
    exact hJ.tmem
  · intro g k d e hg _ hσ he
    exact (fired_kind hpre hX hok hg hσ he).2.1
  · intro g k d hg hG hk hσ
    obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨-, m, rfl⟩ | ⟨hw', -⟩ |
        ⟨hw', -⟩ | ⟨hw', hw'', -⟩
    · rw [prologue_tcKind p]
      refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      have := Progress.Time.prologue_lt_reg p.site
      simp only [stateTime, tmemCnt, tmemS]
      exact this.trans (by decide)
    all_goals (try omega)
    have h := Mma.tmem_time (g := g) (d := m) hpre (by simp at hinv; exact hinv.1)
    simp only [stateTime, tmemCnt, nextKind, mma_tcKind, beq_iff_eq, beq_eq_false_iff_ne]
    exact h

/-- **The store, loader and idle warps' schedule**: they make no warp-collective `tcgen05`
event. -/
theorem noneTcSched :
    Sched.CollSched (timed L) X isTcColl (warpKey L) (fun g => 12 < warpOf L g)
      (fun c k => noneS (Work.n L) (Tc L c.1) k) := by
  have hk0 : ∀ {g j : Nat} {d : ThreadD}, g < L.threads → 12 < warpOf L g →
      j ≤ (X.tr g).length → St L X g j = some (some d) → tcKind (nextKind d) = false := by
    intro g j d hg hG hj hσ
    obtain ⟨-, -, hw⟩ := state_facts hpre hX ht hok hg hj hσ
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨-, s, rfl⟩ | ⟨-, l, rfl⟩ | ⟨hw', -⟩ | ⟨-, s, rfl⟩ |
        ⟨hw', -⟩ | ⟨hw', hw'', -⟩
    · exact prologue_tcKind p
    · obtain ⟨site⟩ := s; cases site <;> rfl
    · cases h : l.site <;> simp [nextKind, loaderKind, tcKind, h]
    all_goals (try omega)
    cases h : s.site <;> simp [nextKind, storeKind, tcKind, h]
  refine Sched.collSched_of (fun _ _ => 0) (fun _ d => tcKind (nextKind d)) ?_ ?_ ?_
    (fun c k => Progress.Time.tail_lt (by omega))
  · intro g k d hg hG hk hσ
    have h := Sched.countP_take_congr (p := isTcColl) (q := fun _ => false) ht hg hσ
      fun {j d' e} hj hσ' he => by
        rw [(fired_kind hpre hX hok hg hσ' he).2.1]
        exact hk0 hg hG (by omega) hσ'
    rw [h]
    simp
  · intro g k d e hg _ hσ he
    exact (fired_kind hpre hX hok hg hσ he).2.1
  · intro g k d hg hG hk hσ
    rw [hk0 hg hG hk hσ]
    refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    simp only [noneS, Nat.add_zero, warpKey]
    show stateTime L g d < tailTime (Work.n L) (Work.T L g) 4000
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨-, s, rfl⟩ | ⟨-, l, rfl⟩ | ⟨hw', -⟩ | ⟨-, s, rfl⟩ |
        ⟨hw', -⟩ | ⟨hw', hw'', -⟩
    · exact Progress.Time.fixed_lt ((Progress.Time.prologue_lt_reg p.site).trans (by decide))
    · exact Idle.time_lt s.site
    · exact (Loader.time_lt hinv).trans (Progress.Time.tail_lt (by decide))
    all_goals (try omega)
    exact (Store.time_lt hinv).trans (Progress.Time.tail_lt (by decide))

/-- **`Cross.TcSched`**, from the correction warps' schedule. -/
theorem tcSched (hcorr : CorrTcSched L X) : TcSched L X := by
  obtain ⟨Sc, hSc⟩ := hcorr
  refine ⟨_, Sched.collSched_union (Q := fun c : Nat × Nat => c.2 < 8)
    ((softTcSched hpre hX ht hok
      (fun hc hi => Softmax.tcColl_sched hc hi)).mono_grp fun g h => h.2)
    (Sched.collSched_union (Q := fun c : Nat × Nat => c.2 < 12) (hSc.mono_grp fun g h => ⟨?_, h.2⟩)
      (Sched.collSched_union (Q := fun c : Nat × Nat => c.2 = 12)
        ((mmaTcSched hpre hX ht hok).mono_grp fun g h => h.2)
        ((noneTcSched hpre hX ht hok).mono_grp fun g h => ?_)))⟩
  · have := h.1.2
    simp only [warpKey] at this
    omega
  · have := h.1.2
    have := h.1.1.2
    have := h.2
    simp only [warpKey] at *
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched

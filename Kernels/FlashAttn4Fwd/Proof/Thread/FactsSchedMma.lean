-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsScheduleRoles

@[expose] public section

/-! # The MMA warp's paired Tensor Memory schedule (`Cross.TmemSched`)

The MMA warp's paired Tensor Memory operations are its allocation (time `allocT`), its
relinquishment and its deallocation (`mmaTail … 0`, `mmaTail … 22`): before a site there are
`Mma.tmemA` of them (`Counts.tmem`). The schedule `tmemS n T k` is the time of the `k`-th, a
time far in the tail after the third. Every other site of the MMA warp is earlier than its next
operation: the fixed sites before the item loop are below `base`, every item site is in a slot of
an item of the cluster (`time_item`), before the tail, and the exit stage is ordered by its offsets.
The two CTAs of a cluster run the same items, so the schedule of the warps 12 of a pair is a
function of the cluster (`Tk`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The items of cluster `c`. -/
def Tk (L : Launch) (c : Nat) : Nat := StaticSchedule.count (Work.G L) (totOf L) c

theorem T_eq (L : Launch) (g : Nat) : Work.T L g = Tk L (L.clusterOfCta (ctaOf L g)) := rfl

theorem T_eq_pair (hpre : Pre P L mem0) (g : Nat) : Work.T L g = Tk L (ctaOf L g / 2) := by
  rw [T_eq]
  simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]

/-! ### The MMA warp's times -/

theorem mmaOff_lt (s : Mma.Site) : mmaOff s < 300 := by
  cases s <;> (repeat' (first | revert ‹Fin _› | revert ‹Bool›)) <;> decide

theorem Mma.time_item_eq {n T : Nat} (d : Mma.D) (hs : Mma.ItemSite d.site) :
    mma n T d = mmaAt n d.i (if Mma.region d.site = 1 then 0 else if Mma.region d.site = 2 then
      d.t + 1 else n) (mmaOff d.site) := by
  unfold mma
  split
  case h_13 => split_ifs <;> rfl
  all_goals simp_all [Mma.ItemSite]

/-- **An item site of the MMA warp is in a slot of an item of the cluster**: after every fixed
time, before the tail. -/
theorem Mma.time_item (hpre : Pre P L mem0) {g : Nat} {d : Mma.D} (hi : Mma.Inv L g d)
    (hs : Mma.ItemSite d.site) :
    base ≤ mma (Work.n L) (Work.T L g) d ∧
      mma (Work.n L) (Work.T L g) d < tailTime (Work.n L) (Work.T L g) 0 := by
  have hIt : d.i < Work.T L g := (Work.mma_work_lt hpre).mp (hi.i hs).1
  have htrip := hi.trip
  have ho := mmaOff_lt d.site
  rw [Mma.time_item_eq d hs]
  have hsl : (if Mma.region d.site = 1 then 0 else if Mma.region d.site = 2 then d.t + 1
      else Work.n L) ≤ Work.n L := by
    unfold Mma.TripOk at htrip
    split_ifs with h1 h2
    · omega
    · simp only [h2] at htrip
      have : Mma.trips L = Work.n L := rfl
      omega
    · omega
  refine ⟨?_, ?_⟩
  · exact Progress.Time.base_le
  · exact Progress.Time.lt_tail hsl hIt (by simp only [bandM, span]; omega)

/-! ### The paired Tensor Memory schedule -/

/-- The time of the MMA warp's `k`-th paired Tensor Memory operation. -/
def tmemS (n T : Nat) : Nat → Nat
  | 0 => allocT
  | 1 => mmaTail n T 0
  | 2 => mmaTail n T 22
  | k + 3 => mmaTail n T (100 + k)

theorem tmemS_mono (n T k : Nat) : tmemS n T k < tmemS n T (k + 1) := by
  match k with
  | 0 => simp only [tmemS, mmaTail, tailTime]; exact Progress.Time.fixed_lt (by decide)
  | 1 => exact Progress.Time.tail_lt (by decide)
  | 2 => exact Progress.Time.tail_lt (by decide)
  | k + 3 => exact Progress.Time.tail_lt (by omega)

theorem Mma.item_tmemA {s : Mma.Site} (hs : Mma.ItemSite s) : Mma.tmemA s = 1 ∧
    mmaKind s ≠ .tmem := by
  cases s <;> simp_all [Mma.ItemSite, Mma.tmemA, mmaKind]

/-- **The MMA warp's sites against its paired Tensor Memory schedule.** -/
theorem Mma.tmem_time (hpre : Pre P L mem0) {g : Nat} {d : Mma.D} (hi : Mma.Inv L g d) :
    (mmaKind d.site = .tmem →
      mma (Work.n L) (Work.T L g) d = tmemS (Work.n L) (Work.T L g) (Mma.tmemA d.site)) ∧
    (mmaKind d.site ≠ .tmem →
      mma (Work.n L) (Work.T L g) d < tmemS (Work.n L) (Work.T L g) (Mma.tmemA d.site)) := by
  by_cases hI : Mma.ItemSite d.site
  · obtain ⟨h1, h2⟩ := Mma.item_tmemA hI
    refine ⟨fun h => absurd h h2, fun _ => ?_⟩
    rw [h1]
    have := (Mma.time_item hpre hi hI).2
    exact this.trans (Progress.Time.tail_lt (by decide))
  · obtain ⟨s, i, t, b, pro⟩ := d
    cases s <;> simp only [Mma.ItemSite, not_true_eq_false] at hI
    all_goals simp only [mma, Mma.tmemA, mmaKind, tmemS, ne_eq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false, IsEmpty.forall_iff, forall_const, true_and, and_true]
    all_goals first
      | decide
      | exact Progress.Time.fixed_lt (by decide)
      | exact Progress.Time.tail_lt (by decide)

/-- The paired Tensor Memory operations before a state of warp 12. -/
def tmemCnt : ThreadD → Nat
  | .inr (.mma m) => Mma.tmemA m.site
  | _ => 0

theorem prologue_not_tmem {es : List Event} (h : ∀ x ∈ es, Prologue.ProKind x.kind) :
    es.countP Tmem.Pair.isTmemOp = 0 := by
  refine List.countP_eq_zero.mpr fun x hx => ?_
  have := h x hx
  obtain ⟨pc, k⟩ := x
  cases k <;> simp_all [Prologue.ProKind, Tmem.Pair.isTmemOp]

theorem prologue_kind_ne_tmem (p : Prologue.D) : nextKind (.inl p) ≠ .tmem := by
  obtain ⟨s⟩ := p
  cases s <;> simp [nextKind, prologueKind]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **`Cross.TmemSched`.** -/
theorem tmemSched : TmemSched L X := by
  refine ⟨fun c k => tmemS (Work.n L) (Tk L c) k,
    Sched.collSched_of (fun _ d => tmemCnt d) (fun _ d => nextKind d == .tmem) ?_ ?_ ?_
      (fun c k => tmemS_mono _ _ k)⟩
  · intro g k d hg hG hk hσ
    obtain ⟨hJ, -, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨-, m, rfl⟩ | ⟨hw', -⟩ |
        ⟨hw', -⟩ | ⟨hw', hw'', -⟩
    · exact prologue_not_tmem hJ.1
    all_goals (try omega)
    exact hJ.tmem
  · intro g k d e hg _ hσ he
    exact (fired_kind hpre hX hok hg hσ he).2.2.1
  · intro g k d hg hG hk hσ
    obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨-, m, rfl⟩ | ⟨hw', -⟩ |
        ⟨hw', -⟩ | ⟨hw', hw'', -⟩
    · have hne := prologue_kind_ne_tmem p
      refine ⟨fun h => absurd (beq_iff_eq.mp h) hne, fun _ => ?_⟩
      have := Progress.Time.prologue_lt_reg p.site
      simp only [stateTime, tmemCnt, tmemS]
      exact this.trans (by decide)
    all_goals (try omega)
    have h := Mma.tmem_time (g := g) (d := m) hpre (by simp at hinv; exact hinv.1)
    simp only [stateTime, tmemCnt, nextKind, beq_iff_eq, beq_eq_false_iff_ne]
    rw [← T_eq_pair hpre g]
    exact h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSt
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWaits
public import Lemmas.Flow.CountSplit

@[expose] public section

/-! # The softmax parts of `Cross.BarAgree` and `Cross.NoRegReentry`

A softmax thread's named-barrier events are its start barrier, one arrival on its statistics
barrier per generation (`n + 1` per item: `gen 0`, `gen 1` per loop trip, `gen 2`) and its end
barrier (`soft_bar`). So its `N`-th one is `softBarAt L g N`: the start barrier for `N = 0`,
the end barrier after the items, else the arrival at the site of generation `(N - 1) % (n + 1)`
of its item. This depends only on the warp (its cluster's item count, its barrier id), so two
lanes of a warp make the same `N`-th named-barrier event. No step of the softmax machine enters
its register request. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The softmax machine never steps to its register request. -/
theorem Softmax.next_ne_setMaxReg {L : Launch} {g : Nat} {d d' : Softmax.D} {e : Event}
    (hn : Softmax.next L g d e = some (some d')) : d'.site ≠ .setMaxReg := by
  intro h
  obtain ⟨site, i, t, w, m, l⟩ := d
  rcases site with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin3_cases j with rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin2_cases c with rfl | rfl)
  all_goals (try cases lp)
  all_goals simp only [Softmax.next, Softmax.nextItem, Softmax.afterStats,
    Softmax.afterLoad] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all

/-- **The softmax part of `Cross.NoRegReentry`.** -/
theorem Cross.NoRegReentry_soft {L : Launch} {g : Nat} {d : Softmax.D} {r' : Role} {e : Event}
    (h : (code L g).next (.inr (.softmax d)) e = some (some (.inr r'))) :
    nextKind (.inr r') ≠ .reg := by
  simp only [code] at h
  rcases hm : Softmax.next L g d e with _ | _ | d'
  · rw [hm] at h; cases h
  · rw [hm] at h; cases h
  · rw [hm] at h
    simp only [Option.map_some, Function.comp_apply, Option.some.injEq, Sum.inr.injEq] at h
    subst h
    have hs := Softmax.next_ne_setMaxReg hm
    simp only [nextKind]
    cases hd : d'.site <;> simp_all [softmaxKind]

/-- The `N`-th named-barrier event of a softmax thread. -/
def softBarAt (L : Launch) (g N : Nat) : Event :=
  if N = 0 then ⟨Softmax.Site.bar0.pc, .bar 2 (some 416) .sync⟩
  else if N = 1 + (Softmax.trips L + 1) * Softmax.items L g then
    ⟨Softmax.Site.barEnd.pc, .bar 2 (some 416) .arrive⟩
  else
    ⟨(if (N - 1) % (Softmax.trips L + 1) = 0 then Softmax.Site.gen 0
      else if (N - 1) % (Softmax.trips L + 1) = Softmax.trips L then Softmax.Site.gen 2
      else Softmax.Site.gen 1).pc, .bar (warpOf L g + 3) (some 64) .arrive⟩

/-- Two lanes of a warp have one barrier sequence. -/
theorem softBarAt_warp {g h : Nat} (hs : SameWarp L g h) (N : Nat) :
    softBarAt L g N = softBarAt L h N := by
  obtain ⟨⟨-, -, hc⟩, hw⟩ := hs
  have hw' : warpOf L g = warpOf L h := hw
  have hi : Softmax.items L g = Softmax.items L h := by
    simp only [Softmax.items, Work.T, Work.cid, clusterOf, ctaOf]
    rw [hc]
  unfold softBarAt
  rw [hi, hw']

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- A softmax thread's named-barrier events before an event split into its start barriers, its
statistics arrivals and its end barriers. -/
theorem soft_isBar_split {g k : Nat} (hw : warpOf L g < 8) :
    ((X.tr g).take k).countP Execution.isBar = barEvents 2 416 .sync ((X.tr g).take k) +
      barEvents (warpOf L g + 3) 64 .arrive ((X.tr g).take k) +
      barEvents 2 416 .arrive ((X.tr g).take k) := by
  unfold barEvents
  apply countP_split3
  intro x hx
  obtain ⟨j, -, hj⟩ := get_of_mem_take hx
  obtain ⟨pc, kd⟩ := x
  cases kd with
  | bar id cnt m =>
    rcases soft_bar hpre hX ht hw hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · cases m <;> simp [Execution.isBar, barIs]
    · simp [Execution.isBar, barIs]
  | _ => simp [Execution.isBar, barIs]

/-- **A softmax thread's `N`-th named-barrier event is `softBarAt L g N`.** -/
theorem soft_bar_at {g i : Nat} {x : Event} (hw : warpOf L g < 8) (he : X.get (g, i) = some x)
    (hb : Execution.isBar x = true) :
    x = softBarAt L g (((X.tr g).take i).countP Execution.isBar) := by
  obtain ⟨pc, kd⟩ := x
  obtain ⟨id, cnt, m, rfl⟩ : ∃ id cnt m, kd = .bar id cnt m := by
    cases kd <;> simp_all [Execution.isBar]
  obtain ⟨d, t, ins, o, -, hc, hi, -, -, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hpc : d.site.pc = pc := (fires_pc hf).symm
  rw [soft_isBar_split hpre hX ht hw, ← soft_statsId, hc.gen, hc.bar2.1, hc.bar2.2]
  have hT := soft_trips_pos hpre
  have hst := hi.start
  have htl := hi.tail
  have hit := hi.item
  have htr := hi.trip
  have hla := hi.last
  have ht0 := hi.tile0
  have hk := soft_statsId L g
  obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
  simp only at hpc hst htl hit htr hla ht0
  subst hpc
  cases site <;> simp only [Softmax.Ev, Kind.bar.injEq, reduceCtorEq, exists_false] at hev
  · obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨rfl, rfl⟩ := hst (.inr rfl)
    simp [softBarAt, Softmax.bar2Sync, Softmax.bar2Arrive, Softmax.genPos, Softmax.Site.tile0,
      Softmax.Site.inTrip]
  case gen j =>
    obtain ⟨rfl, rfl, rfl⟩ := hev
    have hi' := hit rfl
    have hg : ∃ r, Softmax.genPos ⟨.gen j, ii, tt, ww, mm, ll⟩ = r ∧ r ≤ Softmax.trips L ∧
        (j = 0 ↔ r = 0) ∧ (j = 2 ↔ r = Softmax.trips L) := by
      rcases Softmax.fin3_cases j with rfl | rfl | rfl
      · refine ⟨0, by simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
          Softmax.Site.afterGen], by omega, ⟨fun _ => rfl, fun _ => rfl⟩,
          ⟨fun h => absurd h (by decide), fun h => by omega⟩⟩
      · have := htr rfl
        refine ⟨tt + 1, by simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
          Softmax.Site.inTrip, Softmax.Site.afterGen], by omega,
          ⟨fun h => absurd h (by decide), fun h => by omega⟩,
          ⟨fun h => absurd h (by decide), fun h => by omega⟩⟩
      · have := hla (.inr rfl)
        refine ⟨tt + 1, by simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
          Softmax.Site.inTrip, Softmax.Site.afterGen], by omega,
          ⟨fun h => absurd h (by decide), fun h => by omega⟩, ⟨fun _ => by omega, fun _ => rfl⟩⟩
    obtain ⟨r, hr, hrn, h0, h2⟩ := hg
    rw [hr]
    simp only [Softmax.bar2Sync, Softmax.bar2Arrive, Nat.add_zero]
    have hmod : ((1 + ((Softmax.trips L + 1) * ii + r)) - 1) % (Softmax.trips L + 1) = r := by
      rw [show 1 + ((Softmax.trips L + 1) * ii + r) - 1 = (Softmax.trips L + 1) * ii + r by
        omega, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hne : 1 + ((Softmax.trips L + 1) * ii + r) ≠ 1 + (Softmax.trips L + 1) *
        Softmax.items L g := by
      intro heq
      have : (Softmax.trips L + 1) * (ii + 1) ≤ (Softmax.trips L + 1) * Softmax.items L g :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add] at this
      omega
    have hn0 : ¬ (1 + ((Softmax.trips L + 1) * ii + r) = 0) := by omega
    unfold softBarAt
    simp only [hn0, hne, hmod, hk, ↓reduceIte]
    rcases Softmax.fin3_cases j with rfl | rfl | rfl
    · simp [h0.mp rfl]
    · have a1 : ¬ r = 0 := fun h => absurd (h0.mpr h) (by decide)
      have a2 : ¬ r = Softmax.trips L := fun h => absurd (h2.mpr h) (by decide)
      simp [a1, a2]
    · have a1 : ¬ Softmax.trips L = 0 := by omega
      simp [a1, h2.mp rfl]
  · obtain ⟨rfl, rfl, rfl⟩ := hev
    obtain ⟨rfl, rfl⟩ := htl (.inr (.inl rfl))
    simp [softBarAt, Softmax.bar2Sync, Softmax.bar2Arrive, Softmax.genPos, Softmax.Site.tile0,
      Softmax.Site.inTrip]

/-- **The softmax part of `Cross.BarAgree`**: two lanes of a softmax warp make the same
named-barrier event as their `N`-th. -/
theorem Cross.BarAgree_soft {g h i j : Nat} {x y : Event} (hw : warpOf L g < 8)
    (hs : SameWarp L g h) (hx : X.get (g, i) = some x) (hy : X.get (h, j) = some y)
    (hbx : Execution.isBar x = true) (hby : Execution.isBar y = true)
    (hn : ((X.tr g).take i).countP Execution.isBar =
      ((X.tr h).take j).countP Execution.isBar) : x = y := by
  have hw' : warpOf L h < 8 := by
    have : warpOf L g = warpOf L h := hs.2
    omega
  rw [soft_bar_at hpre hX ht hw hx hbx, soft_bar_at hpre hX ht hw' hy hby, hn,
    softBarAt_warp hs]

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof

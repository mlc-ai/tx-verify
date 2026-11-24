-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarSoft

@[expose] public section

/-! # The correction warps' named-barrier schedules against their site table

Barrier 2: the start barrier at `bar0T`, the initial O-free arrivals, every item site and the tail
wait before the end arrival at `tailTime … 2000` (`time_item`), the exit after it (`b2_time`).
The statistics barrier of stage `st`: its syncs are in the slot of their generation, band `C st`
(`+0`, the item's last `+2`); a site of the stage's band after a sync, or of a later band or slot,
is before the next sync in the schedule, a site before it is earlier in its slot
(`sync_time`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Corr

/-- Close a site's comparison with the statistics schedule. -/
macro "stat_close" : tactic => `(tactic| first
  | (apply lt_statS' <;> (try simp only [bandC, span]) <;> omega)
  | (apply lt_same' <;> (try simp only [bandC, span]) <;> (try split_ifs) <;> omega)
  | (apply eq_same' <;> (try simp only [bandC, span]) <;> (try split_ifs) <;> omega))

theorem fin6_cases (x : Fin 6) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  fin_cases x <;> simp

theorem trips_eq : Correction.trips L = Work.n L := rfl

theorem items_eq (L : Launch) (g : Nat) : Correction.items L g = Work.T L g := rfl

/-- **Every item site of a correction warp is before the tail.** -/
theorem time_item {g : Nat} {d : Correction.D} (hi : Correction.Inv L g d)
    (hin : d.site.inItem = true) :
    correction (Work.n L) (Work.T L g) d < tailTime (Work.n L) (Work.T L g) 0 := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  have hiT : i < Work.T L g := hi.item hin
  have htrip := hi.trip
  simp only at htrip hin
  rw [trips_eq] at htrip
  have hb : ∀ (st : Fin 2) (o : Nat), o < 400 → bandC st.val + o < span := fun st o ho => by
    have := st.isLt; simp only [bandC, span]; omega
  cases site with
  | setMaxReg | bar0 | free _ | tailWait | barEnd | exit => simp [Correction.Site.inItem] at hin
  | sync st gen =>
    cases gen
    · exact Progress.Time.lt_tail (by omega) hiT (hb st _ (by decide))
    · exact Progress.Time.lt_tail (by have := htrip rfl; dsimp only; omega) hiT
        (hb st _ (by decide))
    · exact Progress.Time.lt_tail le_rfl hiT (hb st _ (by decide))
  | credit a =>
    fin_cases a
    · exact Progress.Time.lt_tail (by omega) hiT (hb 0 _ (by decide))
    · exact Progress.Time.lt_tail (by have := htrip rfl; dsimp only; omega) hiT (hb 0 _ (by decide))
    · exact Progress.Time.lt_tail (by have := htrip rfl; dsimp only; omega) hiT (hb 1 _ (by decide))
    · exact Progress.Time.lt_tail le_rfl hiT (hb 0 _ (by decide))
    · exact Progress.Time.lt_tail le_rfl hiT (hb 0 _ (by decide))
    · exact Progress.Time.lt_tail le_rfl hiT (hb 1 _ (by decide))
  | ldA st | vote st | rwait st =>
    exact Progress.Time.lt_tail (by have := htrip rfl; dsimp only; omega) hiT (hb st _ (by decide))
  | rld st j | rldW st j | rst st j =>
    exact Progress.Time.lt_tail (by have := htrip rfl; dsimp only; omega) hiT (hb st _ (by omega))
  | oFree st fin =>
    cases fin
    · exact Progress.Time.lt_tail (by have := htrip rfl; dsimp only; omega) hiT
        (hb st _ (by decide))
    · exact Progress.Time.lt_tail le_rfl hiT (hb st _ (by decide))
  | ldL st | oWait st | fWait st | fence st | staged st =>
    exact Progress.Time.lt_tail le_rfl hiT (hb st _ (by decide))
  | fld st j | fldW st j => exact Progress.Time.lt_tail le_rfl hiT (hb st _ (by omega))
  | fst st j h el => exact Progress.Time.lt_tail le_rfl hiT (hb st _ (by omega))

/-- The start and end barriers. -/
def isB2 : Correction.Site → Bool
  | .bar0 | .barEnd => true
  | _ => false

/-- **The correction sites against barrier 2's schedule.** -/
theorem b2_time {g : Nat} {d : Correction.D} (hi : Correction.Inv L g d) :
    (isB2 d.site = true → correction (Work.n L) (Work.T L g) d =
      b2S (Work.n L) (Work.T L g) (Correction.bar2Sync d + Correction.bar2Arrive d)) ∧
    (isB2 d.site = false → correction (Work.n L) (Work.T L g) d <
      b2S (Work.n L) (Work.T L g) (Correction.bar2Sync d + Correction.bar2Arrive d)) := by
  by_cases hin : d.site.inItem = true
  · have h1 : isB2 d.site = false := by
      cases hs : d.site <;> simp_all [isB2, Correction.Site.inItem]
    have h2 : Correction.bar2Sync d + Correction.bar2Arrive d = 1 := by
      cases hs : d.site <;>
        simp_all [Correction.bar2Sync, Correction.bar2Arrive, Correction.Site.inItem]
    rw [h1, h2]
    exact ⟨fun h => absurd h (by simp),
      fun _ => (time_item hi hin).trans (Progress.Time.tail_lt (by decide))⟩
  · obtain ⟨site, i, t, aw, a, o⟩ := d
    cases site with
    | setMaxReg =>
      simp only [correction, isB2, Correction.bar2Sync, Correction.bar2Arrive, b2S]; decide
    | bar0 => simp only [correction, isB2, Correction.bar2Sync, Correction.bar2Arrive, b2S]; decide
    | free st =>
      have := st.isLt
      simp only [correction, isB2, Correction.bar2Sync, Correction.bar2Arrive, b2S, freeT]
      exact ⟨fun h => absurd h (by simp),
        fun _ => Progress.Time.fixed_lt (by simp only [base]; omega)⟩
    | tailWait =>
      simp only [correction, isB2, Correction.bar2Sync, Correction.bar2Arrive, b2S]
      exact ⟨fun h => absurd h (by simp), fun _ => Progress.Time.tail_lt (by decide)⟩
    | barEnd =>
      simp only [correction, isB2, Correction.bar2Sync, Correction.bar2Arrive, b2S]
      exact ⟨fun _ => trivial, fun h => absurd h (by simp)⟩
    | exit =>
      simp only [correction, isB2, Correction.bar2Sync, Correction.bar2Arrive, b2S]
      exact ⟨fun h => absurd h (by simp), fun _ => Progress.Time.tail_lt (by decide)⟩
    | _ => simp [Correction.Site.inItem] at hin

/-- The syncs of stage `st`. -/
def isSync (st : Nat) : Correction.Site → Bool
  | .sync st' _ => st'.val == st
  | _ => false

/-- **The correction sites against stage `st`'s statistics schedule.** -/
theorem sync_time {g st : Nat} {d : Correction.D} (hn : 0 < Work.n L) (hi : Correction.Inv L g d)
    (hst : st < 2) :
    let c := (Work.n L + 1) * d.i + Correction.syncPos L st d
    (isSync st d.site = true → correction (Work.n L) (Work.T L g) d =
      statS (Work.n L) (Work.T L g) (bandC st) 2 c) ∧
    (isSync st d.site = false → correction (Work.n L) (Work.T L g) d <
      statS (Work.n L) (Work.T L g) (bandC st) 2 c) := by
  intro c
  obtain ⟨site, i, t, aw, a, o⟩ := d
  have hitem := hi.item
  have htail := hi.tail
  have hstart := hi.start
  have htrip := hi.trip
  simp only at hitem htail hstart htrip
  rw [trips_eq] at htrip
  rw [items_eq] at hitem htail
  simp only [c]
  rcases (show st = 0 ∨ st = 1 by omega) with rfl | rfl
  all_goals cases site with
    | setMaxReg | bar0 | free _ =>
      have := hstart (by simp)
      subst this
      simp only [isSync, Correction.syncPos, Nat.mul_zero, Nat.zero_add,
        IsEmpty.forall_iff, true_and, Bool.false_eq_true]
      refine fun _ => fixed_lt_statS ?_
      simp only [correction, freeT, regT, bar0T, base]
      omega
    | tailWait | barEnd | exit =>
      have := htail (by simp [Correction.Site.inItem]) (by simp) (by simp) (by simp)
      subst this
      simp only [isSync, Correction.syncPos, Nat.add_zero,
        IsEmpty.forall_iff, true_and, Bool.false_eq_true]
      exact fun _ => tail_lt_statS (by decide)
    | sync st' gen =>
      have hiT := hitem rfl
      fin_cases st' <;> cases gen <;> (try have ht := htrip rfl) <;>
        simp only [correction, isSync, Correction.syncPos, trips_eq, Fin.isValue,
          Fin.zero_eta, Fin.mk_one, beq_iff_eq, reduceCtorEq,
          ↓reduceIte] <;>
        first
          | (refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩; stat_close)
          | (refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩; stat_close)
    | credit a =>
      have hiT := hitem rfl
      rcases fin6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try have ht := htrip rfl) <;>
        simp only [correction, isSync, Correction.syncPos, trips_eq, Fin.isValue, Fin.val_zero,
          Fin.val_one, reduceCtorEq, Bool.false_eq_true,
          ↓reduceIte] <;>
        (refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩; stat_close)
    | ldA st' | vote st' | rwait st' | ldL st' | oWait st' | fWait st' | fence st' | staged st' =>
      have hiT := hitem rfl
      fin_cases st' <;> (try have ht := htrip rfl) <;>
        simp only [correction, isSync, Correction.syncPos, trips_eq, Fin.isValue,
          Fin.zero_eta, Fin.mk_one, reduceCtorEq, Bool.false_eq_true,
          ↓reduceIte] <;>
        (refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩; stat_close)
    | rld st' j | rldW st' j | rst st' j | fld st' j | fldW st' j =>
      have hiT := hitem rfl
      fin_cases st' <;> (try have ht := htrip rfl) <;>
        simp only [correction, isSync, Correction.syncPos, trips_eq, Fin.isValue,
          Fin.zero_eta, Fin.mk_one, reduceCtorEq, Bool.false_eq_true,
          ↓reduceIte] <;>
        (refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩; stat_close)
    | oFree st' fin =>
      have hiT := hitem rfl
      fin_cases st' <;> cases fin <;> (try have ht := htrip rfl) <;>
        simp only [correction, isSync, Correction.syncPos, trips_eq, Fin.isValue,
          Fin.zero_eta, Fin.mk_one, reduceCtorEq, Bool.false_eq_true,
          ↓reduceIte] <;>
        (refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩; stat_close)
    | fst st' j h el =>
      have hiT := hitem rfl
      fin_cases st' <;>
        simp only [correction, isSync, Correction.syncPos, trips_eq, Fin.isValue,
          Fin.zero_eta, Fin.mk_one, reduceCtorEq, Bool.false_eq_true,
          ↓reduceIte] <;>
        (refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩; stat_close)

end Corr
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched

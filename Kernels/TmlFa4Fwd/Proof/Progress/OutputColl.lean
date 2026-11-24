-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Lemmas.Kernel.Progress.Sched
public import Lemmas.Kernel.Progress.Warp
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The warp collectives of warp 13 as a collective schedule

The lanes of warp 13 make one common sequence of warp collectives (`Sched.isWarpColl`): the
startup's three shuffles, the first scan's shuffles and ballot, and, when the first pass picked a
tile, the second scan's after the tail. The time table (`Time.lean`) places the `n`-th of them at
`outSched p c n` for the lane's CTA `c`: the startup's shuffles at their pcs, the first scan's at
`scanBase + 2 n`, the second scan's at `endBase p + 2 n`. The pass of the `n`-th collective is a
function of the CTA (`Late`: the CTA's first pass picked a tile and `n` is past its choice), so
this is a schedule in the library's sense (`out_collSched`, `Sched.CollSched` with key the CTA):
a state whose event is a lane's `n`-th collective is at `outSched p c n`, every other state is
earlier than its next collective.

It is proved from the lane's reference invariant on the thread frame (`Epilogue.good`): the
collectives a lane has made are its ghost counts of shuffles and full-mask ballots (no election, no
warp barrier and no partial ballot occurs on warp 13, `warpColl_eq`), and `Fits` places every state
in the pass its counts say (`PassStart`, `ChosenVals`, `ExitAt`). With `Sched.lag_of_sched` it
gives the lag premise of the warp-collective class for warp 13: a lane of the warp that has made at
most `n` collectives is no later than a lane at its `n`-th. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-! ### The schedule -/

/-- The first pass of CTA `c` picked a tile after scan round `R` with ballot `bal`
(`Epilogue.Picked` with the CTA in place of the lane). -/
def PickedC (p : Params) (c R : Nat) (bal : BitVec 64) : Prop :=
  Epilogue.End p c false R ∧ Epilogue.BalOf p c false R bal ∧
    scmp .ge .s (Epilogue.gxv p c false R) (Epilogue.batchOf p false) = false ∧
    scmp .lt .s (Epilogue.chosen (Epilogue.chosenD p c R bal)) (Epilogue.paramW p.batch) = true

/-- The `n`-th collective of CTA `c`'s output warp belongs to its second pass. -/
def Late (p : Params) (c n : Nat) : Prop :=
  ∃ R bal, PickedC p c R bal ∧ 4 + 7 * (R + 1) + Epilogue.selN bal ≤ n

/-- The pcs of the startup's shuffles. -/
def shPc (n : Nat) : Nat := [25, 34, 35].getD n 0

open Classical in
/-- **The time of the `n`-th warp collective of CTA `c`'s output warp.** -/
def outSched (p : Params) (c n : Nat) : Nat :=
  if Late p c n then endBase p + 2 * n else if n < 3 then shPc n else scanBase + 2 * n

theorem scanBase_lt_endBase (p : Params) : 258 ≤ endBase p := by
  simp only [endBase, tailBase, clk, pipeBase, span]
  omega

theorem late_mono {p : Params} {c n : Nat} (h : Late p c n) : Late p c (n + 1) := by
  obtain ⟨R, bal, hP, hn⟩ := h
  exact ⟨R, bal, hP, by omega⟩

theorem not_late_lt3 {p : Params} {c n : Nat} (hn : n < 3) : ¬ Late p c n := by
  rintro ⟨R, bal, -, h⟩
  omega

theorem outSched_mono (p : Params) (c n : Nat) : outSched p c n < outSched p c (n + 1) := by
  have he := scanBase_lt_endBase p
  have hs : scanBase = 256 := rfl
  unfold outSched
  by_cases h1 : Late p c n
  · simp only [h1, late_mono h1, ↓reduceIte]
    omega
  · rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | h3
    · simp only [h1, not_late_lt3 (show 0 + 1 < 3 by omega), ↓reduceIte]; decide
    · simp only [h1, not_late_lt3 (show 1 + 1 < 3 by omega), ↓reduceIte]; decide
    · have h35 : shPc 2 = 35 := rfl
      simp only [h1, ↓reduceIte]
      split_ifs <;> omega
    · simp only [h1, show ¬ n < 3 from by omega, show ¬ n + 1 < 3 from by omega, ↓reduceIte]
      split_ifs <;> omega

/-- The CTA's choice is the lane's. -/
theorem picked_iff {p : Params} {L : Launch} {g R : Nat} {bal : BitVec 64} :
    Epilogue.Picked p L g R bal ↔ PickedC p (g / L.block) R bal := Iff.rfl

/-- After the choice the schedule is in the second pass. -/
theorem late_of_passStart {p : Params} {L : Launch} {g n0 v0 n : Nat}
    (hP : Epilogue.PassStart p L g true n0 v0) (hn : n0 + v0 ≤ n) : Late p (g / L.block) n := by
  simp only [Epilogue.PassStart, ↓reduceIte] at hP
  obtain ⟨R, bal, hpk, rfl, rfl⟩ := hP
  exact ⟨R, bal, hpk, by omega⟩

/-- Before the choice's last shuffle the schedule is in the first pass. -/
theorem not_late_of_end {p : Params} {L : Launch} {g R n : Nat}
    (hE : Epilogue.End p (g / L.block) false R)
    (hn : ∀ bal, Epilogue.BalOf p (g / L.block) false R bal → n < 4 + 7 * (R + 1) +
      Epilogue.selN bal) :
    ¬ Late p (g / L.block) n := by
  rintro ⟨R', bal, hpk, hle⟩
  obtain rfl := hpk.1.unique hE
  have := hn bal hpk.2.1
  omega

/-! ### Which events are warp collectives -/

/-- The sites of a thread state whose event is a warp collective: a startup shuffle, an output
warp's shuffle or ballot. -/
def isP (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Bool
  | (.inl s, _) => match s.site with | .sh _ => true | _ => false
  | (.inr ⟨.epilogue, d⟩, _) => Out.coll d.site
  | _ => false

/-- The collectives the ghost ledger has counted. -/
def cnt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Nat := collCount σ.2

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An output-warp event is a warp collective exactly at a collective site. -/
theorem out_warpColl {d : Epilogue.D} {e : Event} (hE : Epilogue.Ev p L g d e) :
    Sched.isWarpColl e = Out.coll d.site := by
  obtain ⟨pc, kind⟩ := e
  cases hs : d.site <;> simp only [Epilogue.Ev, hs] at hE <;>
    simp only [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot, Bool.or_false,
      Bool.false_or]
  case store => cases kind <;> simp_all [Epilogue.isStore, Sched.isWarpColl]
  case word | q0 | q1 => rcases hE with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  case start => obtain ⟨_, _, _, rfl⟩ := hE; rfl
  case down | up | total | pre | tiles => obtain ⟨_, _, rfl⟩ := hE; rfl
  case vote => obtain ⟨_, rfl⟩ := hE; rfl
  case ready => obtain ⟨_, rfl⟩ := hE; rfl
  all_goals (subst hE; rfl)

/-- A startup event of warp 13 is a warp collective exactly at a shuffle. -/
theorem start_warpColl {s : Startup.D} {n : Cls → Nat} {e : Event}
    (hS : StartAt L 13 s n) (hE : Startup.Ev L g s e) :
    Sched.isWarpColl e = (match s.site with | .sh _ => true | _ => false) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp only [StartAt] at hS
  case sh j => fin_cases j <;> simp only [Startup.Ev] at hE <;> obtain ⟨_, _, h⟩ := hE <;>
    (subst h; rfl)
  case fence => simp only [Startup.Ev] at hE; subst hE; rfl
  case bar => simp only [Startup.Ev] at hE; subst hE; rfl

/-- **On warp 13 the warp collectives are the shuffles and full-mask ballots.** -/
theorem warpColl_eq (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) : Sched.isWarpColl e = isColl e := by
  by_cases hub : ∃ pc f, e = ⟨pc, .ub f⟩
  · obtain ⟨pc, f, rfl⟩ := hub
    rfl
  push Not at hub
  obtain ⟨⟨σ, n⟩, hσ, hR⟩ := good_state hp hX he hub (Epilogue.good_all hp hX hg hw j)
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · obtain ⟨hE, -, -⟩ := start_fired hp hX he hσ
    have hS := hR.1
    obtain ⟨pc, kind⟩ := e
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [StartAt] at hS
    case sh j => fin_cases j <;> simp only [Startup.Ev] at hE <;> obtain ⟨_, _, h⟩ := hE <;>
      (subst h; rfl)
    case fence => simp only [Startup.Ev] at hE; subst hE; rfl
    case bar => simp only [Startup.Ev] at hE; subst hE; rfl
  · have hE := (Epilogue.fired hp hX he hσ).1
    rw [out_warpColl hE]
    obtain ⟨h1, h2⟩ := Epilogue.ev_counts hE
    have hc := Epilogue.ev_coll hE
    simp only [Out.coll]
    cases hcs : (d.site.shfl || d.site.ballot)
    · simp only [Bool.or_eq_false_iff] at hcs
      simp only [Epilogue.sh, Epilogue.vt, hcs.1, hcs.2, Bool.false_eq_true, ↓reduceIte] at h1 h2
      simp only [isColl]
      split at h1 <;> split at h2 <;> simp_all
    · symm
      apply hc
      simp only [Bool.or_eq_true] at hcs
      rcases hcs with h | h
      · exact .inl h
      · right
        revert h
        cases d.site <;> simp [Epilogue.Site.ballot]
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-! ### The times against the schedule -/

theorem outSched_late {p : Params} {c n : Nat} (h : Late p c n) :
    outSched p c n = endBase p + 2 * n := by
  simp [outSched, h]

theorem outSched_early {p : Params} {c n : Nat} (h : ¬ Late p c n) (h3 : 3 ≤ n) :
    outSched p c n = scanBase + 2 * n := by
  simp [outSched, h, show ¬ n < 3 by omega]

theorem scan_le_outSched (p : Params) (c : Nat) {n : Nat} (h3 : 3 ≤ n) :
    scanBase + 2 * n ≤ outSched p c n := by
  by_cases h : Late p c n
  · rw [outSched_late h]
    have := scanBase_lt_endBase p
    simp only [scanBase] at *
    omega
  · rw [outSched_early h h3]

/-- A state before the end of pass 1's scan round `r` is in the first pass. -/
theorem not_late_reached {p : Params} {c r n : Nat} (hR : Epilogue.Reached p c false r)
    (hn : n ≤ 3 + 7 * r + 7) : ¬ Late p c n := by
  rintro ⟨R', bal', hpk, hle⟩
  have := hR.le_end hpk.1
  have := (Epilogue.selN_pos bal').1
  omega

/-- **The output warp's time against the schedule**: at a collective site the time is the
schedule's time of the lane's collective count, elsewhere earlier. -/
theorem out_time_sched {d : Epilogue.D} {n : Cls → Nat}
    (hF : Epilogue.Fits p L g d (n .shfl) (n .vote)) :
    (Out.coll d.site = true → Out.time p d n = outSched p (g / L.block) (collCount n)) ∧
      (Out.coll d.site = false → Out.time p d n < outSched p (g / L.block) (collCount n)) := by
  have hE := scanBase_lt_endBase p
  have hsb : scanBase = 256 := rfl
  have h3 := Epilogue.fits_three hF
  -- a state of the first pass that is no collective
  have early_nc : ∀ (late : Bool), late = false →
      passTime (if late then endBase p else scanBase) (collCount n) false <
        outSched p (g / L.block) (collCount n) := by
    rintro late rfl
    have := scan_le_outSched p (g / L.block) (show 3 ≤ collCount n by simp only [collCount]; omega)
    simp only [passTime, Bool.false_eq_true, ↓reduceIte]
    unfold collCount at this ⊢
    omega
  -- a state of the second pass
  have late_all : ∀ (b : Bool), Late p (g / L.block) (collCount n) →
      (b = true → passTime (endBase p) (collCount n) b = outSched p (g / L.block) (collCount n))
        ∧ (b = false → passTime (endBase p) (collCount n) b <
          outSched p (g / L.block) (collCount n)) := by
    intro b hl
    rw [outSched_late hl]
    refine ⟨fun hb => by simp [passTime, hb], fun hb => ?_⟩
    simp only [passTime, hb, Bool.false_eq_true, ↓reduceIte, collCount]
    omega
  -- a tail state
  have tail_lt : ∀ R bal, Epilogue.ChosenVals p L g R bal d (n .shfl) (n .vote) →
      Out.tail d.site = true →
      Out.time p d n < outSched p (g / L.block) (collCount n) := by
    intro R bal hC ht
    obtain ⟨hpk, -, -, -, -, -, -, hns, hnv⟩ := hC
    have hl : Late p (g / L.block) (collCount n) := ⟨R, bal, hpk, by simp only [collCount]; omega⟩
    rw [outSched_late hl]
    have := (Out.time_tail (p := p) (n := n) ht).2
    omega
  cases hs : d.site with
  | start =>
    simp only [Epilogue.Fits, hs] at hF
    refine ⟨fun h => by simp [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot] at h, fun _ => ?_⟩
    simp only [Out.time, hs, ↓reduceIte]
    have := scan_le_outSched p (g / L.block) (show 3 ≤ collCount n by simp only [collCount]; omega)
    unfold collCount at this ⊢
    omega
  | word k =>
    simp only [Epilogue.Fits, hs] at hF
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    refine ⟨fun h => by simp [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot] at h, fun _ => ?_⟩
    simp only [Out.time, hs, Out.tail, Out.late, Out.coll, Epilogue.Site.shfl,
      Epilogue.Site.ballot, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    cases hk : k.late
    · exact early_nc false rfl
    · rw [hk] at hP
      exact (late_all false (late_of_passStart hP (by simp only [collCount]; omega))).2 rfl
  | down k | up k _ | total k =>
    simp only [Epilogue.Fits, hs] at hF
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    refine ⟨fun _ => ?_, fun h => by simp [Out.coll, Epilogue.Site.shfl] at h⟩
    simp only [Out.time, hs, Out.tail, Out.late, Out.coll, Epilogue.Site.shfl,
      Bool.true_or, Bool.false_eq_true, ↓reduceIte]
    cases hk : k.late
    · rw [hk] at hP
      have hR1 : Epilogue.Reached p (g / L.block) false r := hk ▸ hR.1
      simp only [Epilogue.PassStart, Bool.false_eq_true, ↓reduceIte] at hP
      obtain ⟨rfl, rfl⟩ := hP
      rw [outSched_early (not_late_reached hR1 (by simp only [collCount]; omega))
        (by simp only [collCount]; omega)]
      simp [passTime]
    · rw [hk] at hP
      exact (late_all true (late_of_passStart hP (by simp only [collCount]; omega))).1 rfl
  | vote l | pre l | tiles l =>
    simp only [Epilogue.Fits, hs] at hF
    obtain ⟨R, n0, v0, hP, hEV, hns, hnv, hrest⟩ := hF
    refine ⟨fun _ => ?_, fun h => by
      simp [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot] at h⟩
    simp only [Out.time, hs, Out.tail, Out.late, Out.coll, Epilogue.Site.shfl,
      Epilogue.Site.ballot, Bool.true_or, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
    cases l
    · simp only [Epilogue.PassStart, Bool.false_eq_true, ↓reduceIte] at hP
      obtain ⟨rfl, rfl⟩ := hP
      have hnl : ¬ Late p (g / L.block) (collCount n) := by
        rintro ⟨R', bal', hpk, hle⟩
        simp only [collCount] at hle
        obtain rfl := hpk.1.unique hEV.1
        have := (Epilogue.selN_pos bal').1
        first
        | omega
        | (obtain ⟨-, hbal, -⟩ := hrest
           obtain rfl := hpk.2.1.unique hbal
           omega)
      rw [outSched_early hnl (by simp only [collCount]; omega)]
      simp [passTime]
    · exact (late_all true (late_of_passStart hP (by simp only [collCount]; omega))).1 rfl
  | q0 =>
    simp only [Epilogue.Fits, hs] at hF
    obtain ⟨R, bal, hC⟩ := hF
    exact ⟨fun h => by simp [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot] at h,
      fun _ => tail_lt R bal hC (by simp [hs, Out.tail])⟩
  | q1 =>
    simp only [Epilogue.Fits, hs] at hF
    obtain ⟨R, bal, hC, -⟩ := hF
    exact ⟨fun h => by simp [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot] at h,
      fun _ => tail_lt R bal hC (by simp [hs, Out.tail])⟩
  | ready _ | store _ _ | commit _ | drain _ | free _ =>
    simp only [Epilogue.Fits, hs] at hF
    obtain ⟨R, bal, hC, -⟩ := hF
    exact ⟨fun h => by simp [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot] at h,
      fun _ => tail_lt R bal hC (by simp [hs, Out.tail])⟩
  | exit l =>
    simp only [Epilogue.Fits, hs, Epilogue.Fits.ExitAt] at hF
    obtain ⟨n0, v0, hP, R, -, hcase⟩ := hF
    refine ⟨fun h => by simp [Out.coll, Epilogue.Site.shfl, Epilogue.Site.ballot] at h, fun _ => ?_⟩
    simp only [Out.time, hs, Out.tail, Out.late, Out.coll, Epilogue.Site.shfl,
      Epilogue.Site.ballot, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    cases l
    · exact early_nc false rfl
    · have hge : n0 + v0 ≤ collCount n := by
        simp only [collCount]
        rcases hcase with ⟨-, h1, h2⟩ | ⟨bal, -, -, h1, h2, -⟩ <;> omega
      exact (late_all false (late_of_passStart hP hge)).2 rfl

/-! ### The schedule on the thread frame -/

/-- The collectives before a state of a lane of warp 13 are its ghost count. -/
theorem cnt_eq (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ((X.tr g).take k).countP Sched.isWarpColl = cnt p L g σ := by
  obtain ⟨σ', n⟩ := σ
  have h1 : ((X.tr g).take k).countP Sched.isWarpColl =
      ((X.tr g).take k).countP isColl := by
    refine List.countP_congr fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hjl : j < (X.tr g).length := by rw [List.length_take] at hj; omega
    have he : X.get (g, j) = some ((X.tr g).take k)[j] := by
      rw [List.getElem_take]
      exact List.getElem?_eq_getElem hjl
    rw [warpColl_eq hp hX hg hw he]
  rw [h1, countColl]
  obtain ⟨hs, hv⟩ := counts hσ
  simp only [cnt, collCount, hs, hv]

/-- The event at a state of a lane of warp 13 is a warp collective exactly at a collective
site. -/
theorem ev_isP (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {σ : (thread p L g).D}
    {e : Event} (hσ : Frame.stateAt (thread p L) X g k = some (some σ))
    (he : X.get (g, k) = some e) : Sched.isWarpColl e = isP p L g σ := by
  obtain ⟨σ', n⟩ := σ
  have hR := (Epilogue.good_all hp hX hg hw k).2 _ hσ
  rcases σ' with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact start_warpColl hR.1 (start_fired hp hX he hσ).1
  · exact out_warpColl (Epilogue.fired hp hX he hσ).1
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-- **The time of a state of a lane of warp 13 against the schedule.** -/
theorem time_sched (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    (isP p L g σ = true → (timed p L).time g σ = outSched p (g / L.block) (cnt p L g σ)) ∧
      (isP p L g σ = false → (timed p L).time g σ < outSched p (g / L.block) (cnt p L g σ)) := by
  obtain ⟨σ', n⟩ := σ
  have hR := (Epilogue.good_all hp hX hg hw k).2 _ hσ
  rcases σ' with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · obtain ⟨hS, hv, -⟩ := hR
    obtain ⟨site, x1, x2, x3⟩ := s
    have h3 : outSched p (g / L.block) 3 = scanBase + 2 * 3 := by
      have := scan_le_outSched p (g / L.block) (le_refl 3)
      by_cases hl : Late p (g / L.block) 3
      · exact absurd hl (by rintro ⟨R, bal, -, h⟩; omega)
      · exact outSched_early hl (le_refl 3)
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      refine ⟨fun _ => ?_, fun h => by simp [isP] at h⟩
      have hc : cnt p L g (.inl ⟨.sh j, x1, x2, x3⟩, n) = j.val := by
        simp only [cnt, collCount, hS.1, hv, Nat.add_zero]
      simp only [hc, outSched, not_late_lt3 j.isLt, j.isLt, ↓reduceIte]
      fin_cases j <;> rfl
    case fence =>
      refine ⟨fun h => by simp [isP] at h, fun _ => ?_⟩
      have hc : cnt p L g (.inl ⟨.fence, x1, x2, x3⟩, n) = 3 := by
        simp only [cnt, collCount, hS.1, hv, Nat.add_zero]
      rw [hc, h3]
      rw [time_start]
      simp [startTime, Startup.Site.pc, scanBase]
    case bar =>
      refine ⟨fun h => by simp [isP] at h, fun _ => ?_⟩
      have hc : cnt p L g (.inl ⟨.bar, x1, x2, x3⟩, n) = 3 := by
        simp only [cnt, collCount, hS.1, hv, Nat.add_zero]
      rw [hc, h3]
      rw [time_start]
      simp [startTime, Startup.Site.pc, scanBase]
  · exact out_time_sched hR.1
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-- **The warp collectives of warp 13 are a collective schedule** of the time table, with key
the CTA and the schedule `outSched`. -/
theorem out_collSched (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) :
    Sched.CollSched (timed p L) X Sched.isWarpColl (fun g => g / L.block) (Epilogue.Q L)
      (outSched p) :=
  Sched.collSched_of (M := timed p L) (cnt p L) (isP p L)
    (fun hg hQ _ hσ => cnt_eq hp hX hg hQ.2 hσ)
    (fun hg hQ hσ he => ev_isP hp hX hg hQ.2 hσ he)
    (fun hg hQ _ hσ => time_sched hp hX hg hQ.2 hσ)
    (outSched_mono p)

/-- **The lag at a warp collective of warp 13**: a lane of the warp that has made at most as many
warp collectives as a lane at one is no later than it. -/
theorem out_lag (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    {σ : (thread p L g).D} {e : Event} (hg : g < L.threads) (hh : h < L.threads)
    (hwg : Prologue.warpIndex L g = 13) (hwh : Prologue.warpIndex L h = 13)
    (hc : h / L.block = g / L.block)
    (hσ : Frame.stateAt (thread p L) X g j = some (some σ)) (he : X.get (g, j) = some e)
    (hcoll : Sched.isWarpColl e = true)
    (hle : (X.tr h).countP Sched.isWarpColl ≤ ((X.tr g).take j).countP Sched.isWarpColl) :
    Sched.threadTime (timed p L) X h ≤ (timed p L).time g σ :=
  Sched.lag_of_sched (out_collSched hp hX) hg hh ⟨hg, hwg⟩ ⟨hh, hwh⟩ hc hσ he hcoll hle

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsElect
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsRounds
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsRefs

@[expose] public section

/-! # `Counts` is a run invariant

It holds at the role's first state for the prologue's trace prefix, which has none of the
counted events but its elections (fourteen in warp 0, none in the other softmax warps), and every
step of the machine keeps it (`counts_step`, from the step of each count). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A trace prefix with none of the events `Counts` counts. -/
structure Quiet (L : Launch) (g : Nat) (es : List Event) : Prop where
  stats : okPolls (ownLoc L g (240 + 8 * stOf L g)) es = 0
  score : okPolls (ownLoc L g (128 + 8 * stOf L g)) es = 0
  pReady : arrivals (leadLoc L g (144 + 8 * stOf L g)) es = 0
  pReady2 : arrivals (leadLoc L g (160 + 8 * stOf L g)) es = 0
  gen : barEvents (kOf L g + 3 + 4 * stOf L g) 64 .arrive es = 0
  bar2 : barEvents 2 416 .sync es = 0 ∧ barEvents 2 416 .arrive es = 0
  tcLd : tcLdsIn (tmem L g 0) (tmem L g 128) es = 0
  tcSt : tcStsIn (tmem L g 64) (tmem L g 128) es = 0
  waitSt : tcWaitSts es = 0
  word : writesAt (statsWord L g) es = 0
  warpBar : es.countP Execution.isWarpBar = 0
  tcColl : es.countP isTcColl = 0
  rounds : ∀ pc, es.countP (okPollAt pc) = 0

theorem counts_start {L : Launch} {g : Nat} {es : List Event} (h : Quiet L g es)
    (hel : es.countP isElectE = if warpOf L g = 0 then 14 else 0) :
    Counts L g start es where
  stats := by rw [h.stats]; rfl
  score := by rw [h.score]; rfl
  pReady := by rw [h.pReady]; rfl
  pReady2 _ := by rw [h.pReady2]; rfl
  pReady2Non _ := h.pReady2
  gen := by rw [h.gen]; rfl
  bar2 := by rw [h.bar2.1, h.bar2.2]; exact ⟨rfl, rfl⟩
  tcLd := by rw [h.tcLd]; rfl
  tcSt := by rw [h.tcSt]; rfl
  waitSt := by rw [h.waitSt]; rfl
  word := by rw [h.word]; rfl
  lead _ h := by simp [start] at h
  warpBar := by rw [h.warpBar]; rfl
  elects := by rw [hel]; rfl
  tcColl := by rw [h.tcColl]; rfl
  rounds s hs := by
    rw [h.rounds]
    rcases s with _ | _ | w | lp | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals (try rcases fin4_cases w with rfl | rfl | rfl | rfl)
    all_goals (try cases lp)
    all_goals simp_all [Site.isPoll, roundOf, start, tailPos, Site.inItem, Site.inTrip]
  words := ⟨fun _ => b32 0, fun c hc => absurd hc (by simp [chunks, start]),
    fun k hk => absurd hk (by simp [chunks, start])⟩
  refs _ _ := ⟨fun h => by simp [start, Site.halved] at h, fun h => by
    simp [start, Site.inTrip] at h⟩

/-- **`Counts` is kept by every step of the machine** whose event has the site's shape. -/
theorem counts_step {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}
    (hi : Inv L g d) (hev : Ev L g d e) (hpc : e.pc = d.site.pc)
    (hn : next L g d e = some (some d')) (hc : Counts L g d es) :
    Counts L g d' (es ++ [e]) where
  stats := step_stats hi hev hn hc.stats
  score := step_score hi hev hn hc.score
  pReady := step_pReady hi hev hn hc.pReady
  pReady2 := step_pReady2 hi hev hn hc.pReady2
  pReady2Non := step_pReady2Non hev hn hc.pReady2Non hc.lead
  gen := step_gen hi hev hn hc.gen
  bar2 := step_bar2 hev hn hc.bar2
  tcLd := step_tcLd hi hev hn hc.tcLd
  tcSt := step_tcSt hi hev hn hc.tcSt
  waitSt := step_waitSt hi hev hn hc.waitSt
  word := counts_step_word hi hev hn hc.word
  lead := step_lead hev hn
  warpBar := counts_step_warpBar hi hev hn hc.warpBar
  elects := counts_step_elects hi hev hn hc.elects
  tcColl := counts_step_tcColl hi hev hn hc.tcColl
  rounds := counts_step_rounds hi hev hpc hn hc.rounds
  words := counts_step_words hi hev hn hc.tcLd hc.words
  refs := counts_step_refs hi hev hn hc.tcLd hc.words hc.refs

/-- The credit of the statistics barrier: before each named-barrier arrival the thread has
one more successful statistics poll than arrivals (the correction warp's `bar.sync` of the
previous generation precedes the credit). -/
theorem credit {L : Launch} {g : Nat} {d : D} {es : List Event} (hi : Inv L g d)
    (hc : Counts L g d es) (j : Fin 3) (hs : d.site = .gen j) :
    barEvents (kOf L g + 3 + 4 * stOf L g) 64 .arrive es + 1 =
      okPolls (ownLoc L g (240 + 8 * stOf L g)) es := by
  rw [hc.gen, hc.stats]
  obtain ⟨site, i, t, s, m, l⟩ := d
  simp only at hs
  subst hs
  have hla := hi.last
  simp only at hla
  rcases fin3_cases j with rfl | rfl | rfl <;>
    simp [genPos, statsPos, tileNo, Site.inItem, Site.tile0, Site.inTrip, Site.afterGen]
      at hla ⊢ <;> omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax

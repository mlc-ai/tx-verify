-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Bar
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemLife
public import Lemmas.Kernel.Progress.Bar

@[expose] public section

/-! # Progress at FA4's named barriers

Every named-barrier event of FA4 is on barrier 2, a group of the warps 0-12 with the operand 416,
or on a statistics barrier `statsId st k`, a group of the softmax warp `k + 4 st` and the
correction warp `8 + k` with the operand 64 (`StatsFacts.bar_form`, `TmemLifeFacts.bar2_warp`).
So each event's barrier has a group (`NamedBar.Shape`) whose arrivals are its warps'
(`NamedBar.Sources`), and the group's warps are those of `BarGroup` (`bar_group`). A participant
lane that has not made its event of a blocked thread's ordinal has not exited and is no later than
the thread's state before its event (`BarWaitFacts.lag_sync`, `lag_warp`), which is earlier than
the thread (`BarWaitFacts.after`). With these the library steps a blocked `bar.sync`
(`bar_steps`, through `Sched.bar_sync_steps`: barrier 2's two generations, the statistics
barriers) and an unrecorded `bar.arrive` (`arrive_steps`, through `Sched.bar_arrive_steps`: the
softmax `gen` arrivals, the softmax and correction `barEnd` arrivals). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The group of a named barrier of an event.** -/
theorem bar_group (hpre : Pre P L mem0) (hst : StatsFacts L X) (hl : TmemLifeFacts L X)
    {g i pc id : Nat} {cnt : Option Nat} {m : BarMode} (hg : g < L.threads)
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) :
    ∃ p : Finset Nat, NamedBar.Shape L cnt p id ∧ NamedBar.Sources L X cnt p id ∧
      ∀ w ∈ p, BarGroup id w := by
  have hb := hpre.block
  rcases hst.bar_form hg he with ⟨rfl, rfl⟩ | ⟨rfl, hw⟩
  · refine ⟨Finset.range 13, ⟨by simp, by simp [CtaBarrier.target], fun w hw => ?_, by decide⟩,
      ?_, fun w hw => .inl ⟨rfl, Finset.mem_range.mp hw⟩⟩
    · rw [hb]
      have := Finset.mem_range.mp hw
      omega
    · rintro ⟨y, j⟩ pc' cnt' ⟨m', he'⟩ hy
      refine ⟨Finset.mem_range.mpr (hl.bar2_warp hy he'), ?_⟩
      rcases hst.bar_form hy he' with ⟨-, h⟩ | ⟨-, ⟨-, h, -⟩ | ⟨h8, -, h | h, -⟩⟩
      · exact h
      all_goals omega
  · obtain ⟨st, k, hst2, hk, hid⟩ : ∃ st k, st < 2 ∧ k < 4 ∧ id = statsId st k := by
      rcases hw with ⟨h8, rfl, -⟩ | ⟨h8, h12, rfl | rfl, -⟩
      · exact ⟨warpOf L g / 4, warpOf L g % 4, by omega, by omega, by unfold statsId; omega⟩
      · exact ⟨0, warpOf L g - 8, by omega, by omega, by unfold statsId; omega⟩
      · exact ⟨1, warpOf L g - 8, by omega, by omega, by unfold statsId; omega⟩
    subst hid
    have hcard : ({k + 4 * st, 8 + k} : Finset Nat).card = 2 := Finset.card_pair (by omega)
    refine ⟨{k + 4 * st, 8 + k}, ⟨by rw [hcard]; decide, ?_, fun w hw => ?_, ?_⟩, ?_,
      fun w hw => .inr ⟨st, k, hst2, hk, rfl, by simpa using hw⟩⟩
    · rw [hcard]
      exact NamedBar.target_some_mul (n := 2) (by decide) (by decide)
    · rw [hb]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      omega
    · unfold statsId; omega
    · rintro ⟨y, j⟩ pc' cnt' ⟨m', he'⟩ hy
      rcases hst.bar_form hy he' with ⟨h2, -⟩ | ⟨hc, hw'⟩
      · unfold statsId at h2; omega
      refine ⟨?_, hc⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [statsId, warpOf] at hw' ⊢
      rcases hw' with ⟨-, h1, -⟩ | ⟨h8, h12, h1 | h1, -⟩ <;> omega

/-- A participant warp of a group lies in `BarGroup`, for a lane of the CTA. -/
theorem barGroup_lane (hb : 0 < L.block) {p : Finset Nat} {id c y : Nat}
    (hp : ∀ w ∈ p, BarGroup id w) (hy : y < L.block) (hyp : y / 32 ∈ p) :
    BarGroup id (warpOf L (c * L.block + y)) := by
  have := (NamedBar.lane_cta (c := c) hb hy).2
  unfold warpOf
  rw [this]
  exact hp _ hyp

/-- A CTA barrier fault makes a consistent execution unsafe. -/
theorem fault_unsafe (hs : SafeGoal kernel asms L mem0) {Y : Execution}
    (hY : Consistent L kernel asms mem0 Y) : ¬ CtaBarFault L Y :=
  fun hf => hs.2 Y hY (by unfold Unsafe; simp [hf])

/-- **Progress at a blocked `bar.sync`.** -/
theorem bar_steps (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hst : ∀ Y, Consistent L kernel asms mem0 Y → StatsFacts L Y)
    (htl : ∀ Y, Consistent L kernel asms mem0 Y → TmemLifeFacts L Y)
    (hbw : ∀ Y, Consistent L kernel asms mem0 Y → BarWaitFacts L Y)
    (htr : Frame.Tracked (code L) X) (hmax : Maximal L kernel asms mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hw : Sched.BarWait L X g) :
    Sched.Steps (timed L) mem0 X (.thread g) := by
  have hX := hmax.1
  obtain ⟨id, cnt, pc, hlen, hlast, -⟩ := hw
  have hg := hp.1
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  obtain ⟨p, hG, hS, hpg⟩ := bar_group hpre (hst X hX) (htl X hX) hg hlast
  obtain ⟨db, hdb⟩ := Frame.state_of_noUb (prologueFacts hpre hX).sound hX htr
    (Sched.safe_noUb (hs.2 X hX)) hlast
  have hgt : stateTime L g db < endTime L X g :=
    Sched.threadTime_after (M := timed L) hlen hdb ((hbw X hX).after hg hlast hdb)
  refine Sched.bar_sync_steps asms_wfStep (fun Y hY => fault_unsafe hs hY) hmax hp hnr hlen hlast
    hG hS fun y hy hyp hle => ?_
  obtain ⟨hnx, hlt⟩ := (hbw X hX).lag_sync hg (NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy)
    (NamedBar.lane_cta hb hy).1 (barGroup_lane hb hpg hy hyp) hlast hdb hle
  exact ⟨hnx, by omega⟩

/-- **Progress at an unrecorded `bar.arrive`.** -/
theorem arrive_steps (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hst : ∀ Y, Consistent L kernel asms mem0 Y → StatsFacts L Y)
    (htl : ∀ Y, Consistent L kernel asms mem0 Y → TmemLifeFacts L Y)
    (hbw : ∀ Y, Consistent L kernel asms mem0 Y → BarWaitFacts L Y)
    (htr : Frame.Tracked (code L) X) (hmax : Maximal L kernel asms mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hw : Sched.ArriveWait L X g) :
    Sched.Steps (timed L) mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨pc, id, cnt, hlast, -⟩ := id hw
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hlast
    simp only at this
    omega
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  obtain ⟨p, hG, hS, -⟩ := bar_group hpre (hst X hX) (htl X hX) hg hlast
  obtain ⟨db, hdb⟩ := Frame.state_of_noUb (prologueFacts hpre hX).sound hX htr
    (Sched.safe_noUb (hs.2 X hX)) hlast
  have hgt : stateTime L g db < endTime L X g :=
    Sched.threadTime_after (M := timed L) hlen hdb ((hbw X hX).after hg hlast hdb)
  refine Sched.bar_arrive_steps asms_wfStep (fault_unsafe hs hX) hmax hp hnr hw hlast hG hS
    fun y hy hyw hle => ?_
  have hyt := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy
  obtain ⟨hdiv, hmod⟩ := NamedBar.lane_cta (c := g / L.block) hb hy
  obtain ⟨hnx, hlt⟩ := (hbw X hX).lag_warp hg hyt ⟨⟨hg, hyt, hdiv.symm⟩, by rw [hmod, hyw]⟩
    hlast hdb hle
  exact ⟨hnx, by omega⟩

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress

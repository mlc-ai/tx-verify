-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.EndTime
import Lemmas.Flow.NotBulk
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
public import Kernels.InklingRelDecode.Proof.Lib.BarClock
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Common.Export.TcLag
import Kernels.InklingRelDecode.Proof.Common.BarState
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

/-! # The clocks of the whole-CTA barrier's lanes

A lane at a rendezvous of barrier 1 is at the clock of its generation (`Lib.barCap` of the number
of earlier rendezvous, at most three). A lane of the CTA with no more rendezvous than that number
has not exited and is no later. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Sched

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A lane at a barrier-1 event is at the clock of its generation.** -/
public theorem bar1_event_clock {j pc cnt md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (he : X.get (g, j) = some ⟨pc, .bar 1 cnt md⟩) :
    ((X.tr g).take j).countP (Execution.isBarId 1) ≤ 3 ∧
      timeAt (schedule Q L) X g j =
        Lib.barCap (((X.tr g).take j).countP (Execution.isBarId 1)) := by
  have hg := Frame.lt_of_get hX he
  have nub := Frame.noUbBefore_of_get hX he
  have nu : ∀ f, (⟨pc, .bar 1 cnt md⟩ : Event).kind ≠ .ub f := by simp
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ f h => nu f (congrArg Event.kind h)) (hf g hg j)
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have cap := bar_cap_state hp hX hf words hg hk hs nub
  have hpc : pc = (thread Q L g).pc s :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  have pub := publication_prefix hp hX hg nub hs
  obtain ⟨_, one | bad | bad⟩ := Lib.recorded_bar hX hp.block he
  all_goals try cases bad.1
  have hb : (thread Q L g).pc s ∈ Lib.barOneSites := hpc ▸ one.2.2
  rw [pub]
  obtain ⟨h3, hc⟩ := cap
  have h3 := h3 hb
  exact ⟨h3, by rw [time_at hs]; exact (hc h3).2.1 hb⟩

/-- **After a barrier-1 event the lane's clock is later.** -/
public theorem bar1_after {j pc cnt md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (he : X.get (g, j) = some ⟨pc, .bar 1 cnt md⟩) :
    timeAt (schedule Q L) X g j < timeAt (schedule Q L) X g (j + 1) := by
  have hg := Frame.lt_of_get hX he
  have nub := Frame.noUbBefore_of_get hX he
  have nu : ∀ f, (⟨pc, .bar 1 cnt md⟩ : Event).kind ≠ .ub f := by simp
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ f h => nu f (congrArg Event.kind h)) (hf g hg j)
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have cap := bar_cap_state hp hX hf words hg hk hs nub
  have hpc : pc = (thread Q L g).pc s :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  have pub := publication_prefix hp hX hg nub hs
  obtain ⟨_, one | bad | bad⟩ := Lib.recorded_bar hX hp.block he
  all_goals try cases bad.1
  have hb : (thread Q L g).pc s ∈ Lib.barOneSites := hpc ▸ one.2.2
  obtain ⟨h3, hc⟩ := cap
  have h3 := h3 hb
  have teq := (hc h3).2.1 hb
  rw [time_at hs]
  rcases h1 : Frame.stateAt (thread Q L) X g (j + 1) with _ | _ | s1
  · rw [time_dead hs h1]; omega
  · exact absurd h1 ((hf g hg (j + 1)).1)
  · have nub1 := NoUbBefore.succ hX he nu
    have hk1 : j + 1 ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    have pub1 := publication_prefix hp hX hg nub1 h1
    have low := bar_low_state hp hX words hk1 h1 nub1
    have step := countP_take_succ (p := Execution.isBarId 1) (g := g) he
      (by simp [Execution.isBarId])
    rw [time_at h1]
    have hp1 : publication s1 = publication s + 1 := by omega
    have := low (by omega) (by omega)
    rw [hp1, Nat.add_sub_cancel] at this
    omega

/-- **A lane with no more barrier-1 events than precede a barrier-1 event has not exited and is
no later than it.** -/
public theorem bar1_lag {y j pc cnt md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (hy : y < L.threads) (nuy : NoUbLane X y)
    (he : X.get (g, j) = some ⟨pc, .bar 1 cnt md⟩)
    (hle : (X.tr y).countP (Execution.isBarId 1) ≤
      ((X.tr g).take j).countP (Execution.isBarId 1)) :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      threadTime (schedule Q L) X y ≤ timeAt (schedule Q L) X g j := by
  obtain ⟨h3, hT⟩ := bar1_event_clock hp hX hf words he
  generalize ((X.tr g).take j).countP (Execution.isBarId 1) = n at *
  have alive {t : Nat} (ht : t ≤ (X.tr y).length) {s : (thread Q L y).D}
      (hs : Frame.stateAt (thread Q L) X y t = some (some s)) :
      ((X.tr y).take t).countP (Execution.isBarId 1) = publication s ∧
        Lib.BarCapAt (siteTime s) ((thread Q L y).pc s) (publication s) :=
    ⟨publication_prefix hp hX hy (nuy.before t) hs,
      bar_cap_state hp hX hf words hy ht hs (nuy.before t)⟩
  have hle' : (X.tr y).countP (Execution.isBarId 1) ≤ n := hle
  refine ⟨fun k pc' hx => ?_, ?_⟩
  · have hk := (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨s, hs, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX hx
      (fun _ f h => by cases h) (hf y hy k)
    have pcx := Frame.event_pcU (fun g hg => thread_sound hp hg) hX hx hs (by simp)
    obtain ⟨_, bad⟩ | ⟨_, _, _, _, hc, fire⟩ := get_source hX hx
    · cases bad
    have ret : pc' = 2855 := by simpa [Lib.retPcs] using Lib.ret_pc' hc fire rfl
    have ph := bar_exit_phase hp hX words hk.le hs (nuy.before k) (pcx.symm.trans ret)
    have pre := publication_prefix hp hX hy (nuy.before k) hs
    have mono := List.Sublist.countP_le (p := Execution.isBarId 1) (List.take_sublist k (X.tr y))
    have := mono
    omega
  · rw [threadTime_eq_timeAt]
    rcases tc_time_cases hf hy (X.tr y).length with hal | h0 | ⟨hpos, hal, hteq⟩
    · obtain ⟨s, hs⟩ := alive_iff.1 hal
      obtain ⟨cnt, cap⟩ := alive le_rfl hs
      rw [List.take_length] at cnt
      have hc : publication s ≤ n := by omega
      have hy3 : publication s ≤ 3 := by omega
      rw [hT, time_at hs]
      exact (cap.2 hy3).1.trans (Lib.barCap_le hc h3)
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨s, hs⟩ := alive_iff.1 hal
      have hlen : (X.tr y).length - 1 < (X.tr y).length := by omega
      obtain ⟨ev, gev⟩ : ∃ ev, X.get (y, (X.tr y).length - 1) = some ev :=
        ⟨_, List.getElem?_eq_getElem hlen⟩
      obtain ⟨cnt, cap⟩ := alive (by omega) hs
      have nu := nuy.kind gev
      have pcx := event_pcU (fun g hg => thread_sound hp hg) hX gev hs nu
      obtain ⟨_, bad⟩ | ⟨_, _, _, _, hc, fire⟩ := get_source hX gev
      · exact absurd bad (nu _)
      have hit := Lib.barOne_fires hp.block hc fire
      have step := countP_take_succ (p := Execution.isBarId 1) (g := y) gev
      rw [hteq, hT, time_at hs]
      have tot : ((X.tr y).take ((X.tr y).length - 1 + 1)).countP (Execution.isBarId 1) ≤ n := by
        rw [Nat.sub_add_cancel (by omega), List.take_length]; exact hle'
      by_cases c : publication s < n
      · have := Lib.barCap_lt c h3
        have := (cap.2 (by omega)).1
        omega
      · have hn : publication s = n := by
          have := List.Sublist.countP_le (p := Execution.isBarId 1)
            (List.take_sublist ((X.tr y).length - 1) (X.tr y))
          omega
        have notb : ¬ (thread Q L y).pc s ∈ Lib.barOneSites := by
          intro hb
          have := step (by rw [hit, pcx]; simpa using hb)
          omega
        have := (cap.2 (by omega)).2.2 notb
        rw [hn] at this
        omega

end PTX.Kernels.InklingRelDecode.Proof.Export

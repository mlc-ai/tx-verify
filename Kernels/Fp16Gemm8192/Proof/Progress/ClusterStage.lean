-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Async
public import Lemmas.Step.Cluster
public import Lemmas.Step.Issue
public import Lemmas.Protocol.ClusterLaneCount

@[expose] public section

/-! # The cluster stages of the rank table

Every thread makes the same four cluster barrier operations: the prologue's arrival and wait, then
the exit's (`ThreadD.clOps`, `clEvent`). A thread that has made fewer of them than another, which
has made at least one, is earlier in the rank table (`time_lt_of_clOps`): the prologue's operations
are at times 50 and 52, every later prologue or role site outside the exit stage is at time 54 or
later, and the exit's operations are at offsets 0 and 2 of the exit stage, which is above every
thread outside it. A thread of a started cluster is not canceled (`not_canceled_of_peer`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {L : Launch} {X : Execution}

/-- The time bounds of a state by its cluster operations. -/
theorem clOps_stage (d : ThreadD) (L : Launch) (g : Nat) (es : List Event) :
    (d.clOps = 0 → d.exitOff = none ∧ d.vtime L g es ≤ 50) ∧
    (d.clOps = 1 → d.exitOff = none ∧ d.vtime L g es = 52) ∧
    (d.clOps = 2 → (d.exitOff = none ∧ 54 ≤ d.vtime L g es) ∨ d.exitOff = some 0) ∧
    (d.clOps = 3 → d.exitOff = some 2) ∧
    (4 ≤ d.clOps → ∃ o, d.exitOff = some o ∧ 4 ≤ o) ∧ d.clOps ≤ 4 := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  · cases site
    case init i =>
      simp [ThreadD.clOps, ThreadD.exitOff, ThreadD.vtime, Prologue.Site.vtime]
      omega
    all_goals simp [ThreadD.clOps, ThreadD.exitOff, ThreadD.vtime, Prologue.Site.vtime]
  · cases site <;> simp [ThreadD.clOps, ThreadD.exitOff, ThreadD.vtime, Loader.vtime,
      Loader.exitOff, ringAt, blockAt] <;> omega
  · cases site <;> simp [ThreadD.clOps, ThreadD.exitOff, ThreadD.vtime, Mma.vtime, Mma.exitOff,
      ringAt, blockAt] <;> omega
  · cases site <;> simp [ThreadD.clOps, ThreadD.exitOff, ThreadD.vtime, Scheduler.vtime,
      Scheduler.exitOff, blockAt] <;> omega
  · cases site <;> simp [ThreadD.clOps, ThreadD.exitOff, ThreadD.vtime, Consumer.vtime,
      Consumer.exitOff, blockAt] <;> omega

/-- Every thread's operation `n` is a cluster operation at its site. -/
theorem clEvent_shape (n : Nat) : ∃ op, clEvent n = ⟨(clEvent n).pc, .cluster op⟩ := by
  rcases n with _ | _ | _ | n <;> exact ⟨_, rfl⟩

/-- The operations `0` and `2` are arrivals. -/
theorem clEvent_arrive {n : Nat} (h : n = 0 ∨ n = 2) :
    clEvent n = ⟨(clEvent n).pc, .cluster (.arrive true true)⟩ := by
  rcases h with rfl | rfl <;> rfl

/-- The operations `1` and `3` are waits. -/
theorem clEvent_wait {n : Nat} (h : n = 1 ∨ n = 3) :
    clEvent n = ⟨(clEvent n).pc, .cluster (.wait true)⟩ := by
  rcases h with rfl | rfl <;> rfl

/-- A thread in the exit stage is at its offset above `exitBase`. -/
theorem threadTime_exit {g o : Nat} {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (he : d.exitOff = some o) :
    threadTime L X g = exitBase L X + o := by
  simp [threadTime, hσ, he]

/-- A thread outside the exit stage is below `exitBase`. -/
theorem threadTime_lt_exitBase {g : Nat} {d : ThreadD} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (he : d.exitOff = none) :
    threadTime L X g < exitBase L X := by
  have h1 := baseTime_lt_exitBase (X := X) hg
  have h2 : baseTime L X g = d.vtime L g (X.tr g) := by simp [baseTime, hσ, he]
  rw [threadTime_of hσ he]
  omega

/-- **A thread with fewer cluster operations is earlier**: a thread that is dead, or has made
fewer cluster operations than a thread that has made one, has a smaller time. -/
theorem time_lt_of_clOps {g h : Nat} {dg : ThreadD} (hh : h < L.threads)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some dg)) (h1 : 1 ≤ dg.clOps)
    (hσh : Frame.stateAt (code L) X h (X.tr h).length = none ∨
      ∃ dh, Frame.stateAt (code L) X h (X.tr h).length = some (some dh) ∧ dh.clOps < dg.clOps) :
    threadTime L X h < threadTime L X g := by
  have sg := clOps_stage dg L g (X.tr g)
  have hgpos : 1 ≤ threadTime L X g := by
    have hb : 1 ≤ exitBase L X := by simp only [exitBase]; omega
    rcases Nat.lt_or_ge dg.clOps 2 with h2 | h2
    · obtain ⟨he, hv⟩ := sg.2.1 (by omega)
      rw [threadTime_of hσg he]
      omega
    rcases Nat.lt_or_ge dg.clOps 3 with h3 | h3
    · rcases sg.2.2.1 (by omega) with ⟨he, hv⟩ | he
      · rw [threadTime_of hσg he]
        omega
      · rw [threadTime_exit hσg he]
        omega
    rcases Nat.lt_or_ge dg.clOps 4 with h4 | h4
    · rw [threadTime_exit hσg (sg.2.2.2.1 (by omega))]
      omega
    · obtain ⟨o, he, -⟩ := sg.2.2.2.2.1 h4
      rw [threadTime_exit hσg he]
      omega
  rcases hσh with hn | ⟨dh, hσh, hlt⟩
  · have h0 : threadTime L X h = 0 := by simp [threadTime, hn]
    omega
  have sh := clOps_stage dh L h (X.tr h)
  -- the time of `h`, by its count
  rcases Nat.lt_or_ge dg.clOps 2 with h2 | h2
  · obtain ⟨heg, hvg⟩ := sg.2.1 (by omega)
    obtain ⟨heh, hvh⟩ := sh.1 (by omega)
    rw [threadTime_of hσg heg, threadTime_of hσh heh]
    omega
  rcases Nat.lt_or_ge dg.clOps 3 with h3 | h3
  · have hdh : dh.clOps = 0 ∨ dh.clOps = 1 := by omega
    have hvh : dh.exitOff = none ∧ dh.vtime L h (X.tr h) ≤ 52 := by
      rcases hdh with hd | hd
      · obtain ⟨a, b⟩ := sh.1 hd
        exact ⟨a, by omega⟩
      · obtain ⟨a, b⟩ := sh.2.1 hd
        exact ⟨a, by omega⟩
    rw [threadTime_of hσh hvh.1]
    rcases sg.2.2.1 (by omega) with ⟨heg, hvg⟩ | heg
    · rw [threadTime_of hσg heg]
      omega
    · rw [threadTime_exit hσg heg]
      have := threadTime_lt_exitBase hh hσh hvh.1
      rw [threadTime_of hσh hvh.1] at this
      omega
  -- `g` is in the exit stage, past its arrival there
  have hgt : exitBase L X + 2 ≤ threadTime L X g ∧
      (4 ≤ dg.clOps → exitBase L X + 4 ≤ threadTime L X g) := by
    rcases Nat.lt_or_ge dg.clOps 4 with h4 | h4
    · rw [threadTime_exit hσg (sg.2.2.2.1 (by omega))]
      exact ⟨le_refl _, fun h => by omega⟩
    · obtain ⟨o, he, ho⟩ := sg.2.2.2.2.1 h4
      rw [threadTime_exit hσg he]
      exact ⟨by omega, fun _ => by omega⟩
  -- `h` is at most at the exit stage's wait
  have hth : threadTime L X h ≤ exitBase L X + 2 ∧
      (dh.clOps ≤ 2 → threadTime L X h ≤ exitBase L X) := by
    rcases Nat.lt_or_ge dh.clOps 2 with k2 | k2
    · have hnone : dh.exitOff = none := by
        rcases Nat.lt_or_ge dh.clOps 1 with k1 | k1
        · exact (sh.1 (by omega)).1
        · exact (sh.2.1 (by omega)).1
      have := threadTime_lt_exitBase hh hσh hnone
      exact ⟨by omega, fun _ => by omega⟩
    rcases Nat.lt_or_ge dh.clOps 3 with k3 | k3
    · rcases sh.2.2.1 (by omega) with ⟨he, -⟩ | he
      · have := threadTime_lt_exitBase hh hσh he
        exact ⟨by omega, fun _ => by omega⟩
      · rw [threadTime_exit hσh he]
        exact ⟨by omega, fun _ => by omega⟩
    · have hd3 : dh.clOps = 3 := by omega
      rw [threadTime_exit hσh (sh.2.2.2.1 hd3)]
      exact ⟨le_refl _, fun h => by omega⟩
  rcases Nat.lt_or_ge dg.clOps 4 with h4 | h4
  · have := hth.2 (by omega)
    omega
  · have := hgt.2 h4
    omega

/-- A thread of a cluster in which some thread has an event is not canceled. -/
theorem not_canceled_of_peer {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {g h : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block)) : ¬ ClcCanceled L X h := by
  rintro ⟨-, r, hr⟩
  obtain ⟨i, s, ts, -, his, -⟩ := hX.clc.canceled_has_issue hr
  rw [hc] at hr
  exact hX.clc.running_not_canceled ⟨i, s, ts, his⟩ hg hne hr

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress

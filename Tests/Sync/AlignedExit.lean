-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

/-! Litmus tests for the exit clause of ERR-ALIGNED-MISMATCH (one CTA of two warps).

`skipped`: warp 0 exits and warp 1 executes an aligned whole-CTA `bar.sync 0`. The CTA-level
`.aligned` sentence (§9.7.15.1) makes this undefined: the execution is `Unsafe`
(`skipped_unsafe`).

`clusterSkipped`: lane 0 of a warp exits and lane 1 executes an aligned `barrier.cluster.arrive`:
the `.aligned` sentence of §9.7.15.3 is warp-level, and this execution is `Unsafe`
(`clusterSkipped_unsafe`).

`tcSkipped`: lane 0 exits and lane 1 executes `tcgen05.wait::ld` (warp participants,
`tcSkipped_mismatch`). `tcSplit`: lanes 0 and 1 execute their first `tcgen05.wait::ld` at two
positions (`tcSplit_mismatch`).

`regSkipped`: thread 32 (warp 1) exits and thread 0 executes `setmaxnreg`. The participants of
`setmaxnreg` are the warpgroup, which holds both threads (`regSkipped_mismatch`).

`joined`: every thread executes the barrier and then exits. No thread exits short of the
barrier, so the exit clause of `AlignedMismatch` does not hold (`joined_not_exitedShort`). -/

namespace PTX.Tests.AlignedExit
open PTX

private def L : Launch := { grid := 1, block := 64, params := fun _ => none }

private def K : Kernel :=
  { name := "aligned_exit", params := [], code := [{ op := .barSync (.imm 0) true }] }

private def barEv : Event := ⟨0, .bar 0 none⟩
private def exitEv : Event := ⟨1, .exit⟩

private def skipped : Execution :=
  { tr := fun g => if g < 32 then [exitEv] else if g < 64 then [barEv, exitEv] else []
    rf := fun _ _ => none }

private def joined : Execution :=
  { tr := fun g => if g < 64 then [barEv, exitEv] else []
    rf := fun _ _ => none }

private theorem barEv_aligned : K.isAlignedCtaBar barEv = true := rfl

theorem skipped_mismatch : AlignedMismatch L K skipped :=
  ⟨.bar, .inr ((AlignedClass.exited_bar_iff L).2 ⟨(32, 0), (0, 0), 0,
    ⟨by simp [L, Launch.threads], by simp [L, Launch.threads], by simp [L]⟩,
    ⟨barEv, by simp [skipped, Execution.get], barEv_aligned⟩, rfl,
    ⟨1, by simp [skipped, Execution.get, exitEv]⟩,
    by simp [skipped, exitEv, Kernel.isAlignedCtaBar]⟩)⟩

theorem skipped_unsafe (A : List Assumption) (mem0 : Mem0) : Unsafe L K A mem0 skipped :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl skipped_mismatch))))))))

theorem joined_not_exitedShort (e f : EvId) (k : Nat)
    (he : ∃ ev, joined.get e = some ev ∧ K.isAlignedCtaBar ev = true)
    (hk : ((joined.tr e.1).take e.2).countP K.isAlignedCtaBar = k) :
    ¬ joined.ExitedShort K.isAlignedCtaBar f k := by
  rintro ⟨⟨pcx, hf⟩, hs⟩
  obtain ⟨ev, hev, hal⟩ := he
  obtain ⟨g, j⟩ := e
  have hg : g < 64 := by
    by_contra h
    simp [joined, Execution.get, h] at hev
  have hj : j = 0 := by
    rcases j with _ | _ | j
    · rfl
    · simp [joined, Execution.get, hg, exitEv] at hev
      subst hev
      simp [Kernel.isAlignedCtaBar] at hal
    · simp [joined, Execution.get, hg] at hev
  subst hj
  simp at hk
  have hf1 : f.1 < 64 := by
    by_contra h
    simp [joined, Execution.get, h] at hf
  have : (joined.tr f.1).countP K.isAlignedCtaBar = 1 := by
    simp [joined, hf1, barEv, exitEv, Kernel.isAlignedCtaBar, Kernel.alignedAt, K, Op.aligned]
  omega

private def clusterEv : Event := ⟨0, .cluster (.arrive true true)⟩

private def clusterSkipped : Execution :=
  { tr := fun g => if g = 0 then [exitEv] else if g = 1 then [clusterEv, exitEv] else []
    rf := fun _ _ => none }

theorem clusterSkipped_mismatch : AlignedMismatch L K clusterSkipped :=
  ⟨.cluster, .inr ((AlignedClass.exited_cluster_iff L).2 ⟨(1, 0), (0, 0), 0, 0,
    .arrive true true, ⟨⟨by simp [L, Launch.threads], by simp [L, Launch.threads], by simp [L]⟩,
    by simp [L]⟩, by simp [clusterSkipped, Execution.get, clusterEv], rfl, rfl,
    ⟨1, by simp [clusterSkipped, Execution.get, exitEv]⟩,
    by simp [clusterSkipped, exitEv, isCluster]⟩)⟩

theorem clusterSkipped_unsafe (A : List Assumption) (mem0 : Mem0) :
    Unsafe L K A mem0 clusterSkipped :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl clusterSkipped_mismatch))))))))

/-! ## `tcgen05` and `setmaxnreg` -/

private def waitEv (pc : Nat) : Event := ⟨pc, .tc .waitLd⟩

private def tcSkipped : Execution :=
  { tr := fun g => if g = 0 then [exitEv] else if g = 1 then [waitEv 0, exitEv] else []
    rf := fun _ _ => none }

theorem tcSkipped_mismatch : AlignedMismatch L K tcSkipped :=
  ⟨.tc, .inr ((AlignedClass.exited_tc_iff L).2 ⟨(1, 0), (0, 0), 0,
    ⟨⟨by simp [L, Launch.threads], by simp [L, Launch.threads], by simp [L]⟩, by simp [L]⟩,
    ⟨⟨waitEv 0, by simp [tcSkipped, Execution.get], rfl⟩, rfl⟩,
    ⟨1, by simp [tcSkipped, Execution.get, exitEv]⟩, by simp [tcSkipped, exitEv, isTcColl]⟩)⟩

private def tcSplit : Execution :=
  { tr := fun g => if g = 0 then [waitEv 0] else if g = 1 then [waitEv 1] else []
    rf := fun _ _ => none }

theorem tcSplit_mismatch : AlignedMismatch L K tcSplit :=
  ⟨.tc, .inl ((AlignedClass.divergent_tc_iff L).2 ⟨(0, 0), (1, 0), 0, 0, 1, .waitLd, .waitLd,
    ⟨⟨by simp [L, Launch.threads], by simp [L, Launch.threads], by simp [L]⟩, by simp [L]⟩,
    ⟨⟨waitEv 0, by simp [tcSplit, Execution.get], rfl⟩, rfl⟩,
    ⟨⟨waitEv 1, by simp [tcSplit, Execution.get], rfl⟩, rfl⟩,
    by simp [tcSplit, Execution.get, waitEv], by simp [tcSplit, Execution.get, waitEv],
    .inl (by decide)⟩)⟩

private def regEv : Event := ⟨0, .setMaxReg false 72 0⟩

private def regSkipped : Execution :=
  { tr := fun g => if g = 32 then [exitEv] else if g = 0 then [regEv, exitEv] else []
    rf := fun _ _ => none }

theorem regSkipped_mismatch : AlignedMismatch L K regSkipped :=
  ⟨.setMaxReg, .inr ⟨(0, 0), (32, 0), regEv,
    show SameWarpgroup L 0 32 from
      ⟨⟨by simp [L, Launch.threads], by simp [L, Launch.threads], by simp [L]⟩, by simp [L]⟩,
    by simp [regSkipped, Execution.get], rfl, rfl,
    ⟨⟨1, by simp [regSkipped, Execution.get, exitEv]⟩,
      by simp [regSkipped, exitEv, AlignedClass.exitMember, AlignedClass.member,
        SetMaxNReg.isRequest]⟩⟩⟩

end PTX.Tests.AlignedExit

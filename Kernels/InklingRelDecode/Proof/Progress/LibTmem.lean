-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Remaining
public import Kernels.InklingRelDecode.Proof.Progress.LibTmem1Ready

@[expose] public section

/-!
# `Remaining.tmemSteps`: the `cta_group::1` Tensor Memory allocator makes progress

The kernel's Tensor Memory operations are made by warp 0 of each CTA alone, `cta_group::1`: an
allocation of 512 columns, a relinquishment and a deallocation, in that order (`Tmem1Ops`). A
CTA's allocator performs such an operation, a counted extension (`Step.warp_entry_counted`), as
soon as every lane of the warp has made it (`Tmem1.tmem1_step`, `LibTmem1Ready.lean`); until then
a lane of the warp has made fewer operations, is pending (a lane of the warp exits after its three
operations, `Tmem1Facts.exit`) and, by the warp-collective `tcgen05` facts, earlier in the rank
table (`Sched.TcWaitFacts`: the allocator operations are warp-collective `tcgen05` events,
`isTcColl`).

* A blocked pending thread at an operation (`Sched.TmemOpen`): the operation is not performed, since
  every record of a `cta_group::1` history is a covered operation (`covered_of_performed`); the
  warp's record is a counted extension, or a lane of the warp that has made no more operations is
  pending and earlier than the blocked thread, which `tc_le_of_ops` turns into the hypothesis of
  `TcWaitFacts.lag`.
* An open paired-request obligation (`Descent.Obl .tmem`): an uncovered operation, so the same
  dichotomy: a counted extension, or a pending lane, which ranks below the obligation
  (`Sched.rank_thread_lt_tmem`).

`tmemSteps_of` is `Remaining.tmemSteps`; it takes the protocol layer's `Tmem1Facts` of every
consistent execution and the `tcWaits` field of `Remaining`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface Tmem.Pair
  PTX.Kernels.InklingRelDecode.Proof.Tmem1

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {w : Nat}

/-- In a `cta_group::1` execution a performed operation is covered. -/
theorem covered_of_performed (hX : Consistent L kernel asms mem0 X) (ht : Tmem1Ops L X w)
    {i : EvId} (hp : Performed L X i) : Covered L X i := by
  obtain ⟨cta, x, hx, hpa⟩ := hp
  obtain ⟨-, -, hxg, -⟩ := record_info hX ht hx
  exact ⟨[x.own], .inl ⟨cta, x, hx, hxg, rfl⟩, x.own, List.mem_singleton_self _, hpa⟩

/-- A lane of warp `w` that has made at most `n` operations has not exited. -/
theorem lane_pending (hX : Consistent L kernel asms mem0 X) (ht : Tmem1Facts L X w) {g h n : Nat}
    (hg : g % L.block / 32 = w) (hw : SameWarp L g h) (hn : n < 3)
    (hle : tmemOps (X.tr h) ≤ n) : Frame.Pending L X h := by
  refine pending_of_noExit hX hw.1.2.1 fun j pc hj => ?_
  have h3 := ht.exit hw.1.2.1 (by rw [← hw.2]; exact hg) hj
  have h4 : tmemOps ((X.tr h).take j) ≤ tmemOps (X.tr h) := (List.take_sublist _ _).countP_le
  omega

/-- **The step of an unperformed operation**: a counted extension, or a pending lane of the warp
that is earlier than the thread `g` at the operation (`g`'s state after it is later than its
state before it, and a lane that has made at most as many operations is no later than the state
before). -/
theorem tmem_op_cases (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hsafe : ¬ Unsafe L kernel asms mem0 X) (ht : Tmem1Facts L X 0) {g j pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request} (hg : g < L.threads)
    (hge : X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩) (hnp : ¬ Performed L X (g, j)) :
    (∃ Y, Consistent L kernel asms mem0 Y ∧ X.le Y ∧ X.size L < Y.size L) ∨
      ∃ h, Frame.Pending L X h ∧ SameWarp L g h ∧ tmemOps (X.tr h) ≤ tmemOps ((X.tr g).take j) := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hop : TmemOp X g (tmemOps ((X.tr g).take j)) j := ⟨⟨_, _, _, _, hge⟩, rfl⟩
  obtain ⟨hwg, -, hsh⟩ := ht.event hg hge
  have hn3 : tmemOps ((X.tr g).take j) < 3 := lt_of_tmemShape hsh
  rcases tmem1_step hX ht.toTmem1Ops (Sched.safe_noAligned hsafe) hb hg hop hnp
    (fun a ha c r => asms_wfStep.quiet hX le_recordEntry rfl (Execution.noNewRead_of_tr rfl)
      a ha) with
    ⟨Y, hY, hle, -, hsize⟩ | ⟨h, hw, hle⟩
  · exact .inl ⟨Y, hY, hle, hsize⟩
  · exact .inr ⟨h, lane_pending hX ht hwg hw hn3 hle, hw, hle⟩

/-- **A blocked pending thread at a Tensor Memory operation steps.** -/
theorem tmem_wait_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (ht : Tmem1Facts L X 0) (hw : Sched.TcWaitFacts (timed T Q L) X)
    (hmax : Maximal L kernel asms mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) (htw : Sched.TmemOpen L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  obtain ⟨pc, grp, dst, act, hlast, hnr⟩ := htw
  have hX := hmax.1
  have hg := hp.1
  have hsafe := hs.2 X hX
  have hub := Sched.safe_noUb hsafe
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
    omega
  have hnp : ¬ Performed L X (g, (X.tr g).length - 1) := fun hpf =>
    hnr ⟨hpf, fun _ => covered_of_performed hX ht.toTmem1Ops hpf⟩
  rcases tmem_op_cases hpre hX hsafe ht hg hlast hnp with ⟨Y, hY, hle, hsize⟩ |
    ⟨h, hph, hsw, hle⟩
  · exact .inl ⟨Y, hY, hle, hsize⟩
  · have hop : TmemOp X g (tmemOps ((X.tr g).take ((X.tr g).length - 1)))
        ((X.tr g).length - 1) := ⟨⟨_, _, _, _, hlast⟩, rfl⟩
    have hk : X.TcK (g, (X.tr g).length - 1)
        (tcCount X g ((X.tr g).length - 1)) := tcK_of_op hop
    have hle' := tc_le_of_ops ht.toTmem1Ops (Sched.safe_noAligned hsafe) hsw hop hle
    obtain ⟨d, hd⟩ := Frame.state_of_noUb (C := code L Q) hS hX htr hub hlast
    have h1 : Sched.threadTime (timed T Q L) X h ≤ T g d := hw.lag hg hph.1 hsw hk hd hle'
    have h2 : T g d < Sched.threadTime (timed T Q L) X g :=
      Sched.threadTime_after hlen hd (hw.after hg hk hd)
    exact Sched.earlier_steps hmax hrel hph (by omega)

/-- **An open paired-request obligation steps**: an uncovered operation is not performed; the
warp's record is a counted extension, or a pending lane of the warp ranks below the obligation. -/
theorem tmem_obl_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (ht : Tmem1Facts L X 0) (hmax : Maximal L kernel asms mem0 X) (ho : Descent.Obl L X .tmem) :
    Sched.Steps (timed T Q L) mem0 X .tmem := by
  have hX := hmax.1
  have hsafe := hs.2 X hX
  simp only [Descent.Obl, Drained, not_forall] at ho
  obtain ⟨i, pc, group, dst, action, hget, hn⟩ := ho
  have hnp : ¬ Performed L X i := fun hpf => hn (covered_of_performed hX ht.toTmem1Ops hpf)
  obtain ⟨g, j⟩ := i
  rcases tmem_op_cases hpre hX hsafe ht (Frame.lt_of_get hX hget) hget hnp with
    ⟨Y, hY, hle, hsize⟩ | ⟨h, hph, -, -⟩
  · exact .inl ⟨Y, hY, hle, hsize⟩
  · exact .inr ⟨X, .thread h, hmax, hph, Sched.rank_thread_lt_tmem hph.1⟩

/-- **`Remaining.tmemSteps`**: the `cta_group::1` Tensor Memory allocator makes progress, given the
protocol layer's Tensor Memory facts of warp 0 (`Tmem1Facts`) and the warp-collective `tcgen05`
facts (`Remaining.tcWaits`). -/
theorem tmemSteps_of (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (htr : ∀ Y, Consistent L kernel asms mem0 Y → Frame.Tracked (code L Q) Y)
    (ht : ∀ X, Consistent L kernel asms mem0 X → Tmem1Facts L X 0)
    (hw : ∀ X, Consistent L kernel asms mem0 X → Sched.TcWaitFacts (timed T Q L) X) :
    TmemSteps T Q L mem0 :=
  ⟨fun X _ hmax hp hrel htw => tmem_wait_steps hpre hs hS (htr X hmax.1) (ht X hmax.1)
      (hw X hmax.1) hmax hp hrel htw,
    fun X hmax ho => tmem_obl_steps hpre hs (ht X hmax.1) hmax ho⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Progress

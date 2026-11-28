-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollKey
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfAppend
public import Lemmas.Quiet.Progress.Released
public import Lemmas.Kernel.Progress.WarpVoteSteps
public import Lemmas.Kernel.Progress.NextEv
public import Lemmas.Kernel.Progress.FaultExtension
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0VoteLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0VoteRel
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0VoteTmpl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollClsOf
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.PendAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.PendAtView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode

@[expose] public section

/-! # A released lane at the vote steps

`vote_quiet_steps`: a pending released lane whose next event is at the vote of warpgroup 0 (pc
578, the only mode vote of the code) steps, given the kernel's vote facts `VoteRel` (one
`Sched.WarpVoteRel` of the glued thread machine, keyed by the warp) and that every lane has
drained its selected stores. `vote_rel` proves them for every consistent execution that follows
the role tables: the template names the full mask (`w0_vote_tmpl`), a lane at the vote is released
(`w0_vote_rel`), the block count bounds the votes (`vote_cnt_lt`, `vote_cnt_exit`), and the lag
is the order of places (`vote_lag`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- **The kernel's vote facts** for one execution. -/
@[no_expose] def VoteRel (P : Params) (L : Launch) (m : Mem0) (X : Execution) : Prop :=
  Sched.WarpVoteRel m ⟨thread P L, time P L⟩ X (warpKey L) (VoteAt P L) 578 (2 ^ 32 - 1) .any

/-- A lane's warp is below 4 as its key says. -/
private theorem warp_key (hp : Pre P L m) (y : Nat) :
    warpOf L y < 4 ↔ (warpKey L y).2 < 4 := by
  simp only [warpOf, tidOf, tidOf_x_eq hp, warpKey, hp.block]

/-- **The vote facts**, given every barrier's participant group. -/
theorem vote_rel (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X)
    (hgrp : ∀ {g i pc id : Nat} {cnt : Option Nat} {md : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt md⟩ →
      ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id) :
    VoteRel P L m X := by
  unfold VoteRel
  refine ⟨?_, ?_, ⟨fun k => if k.2 < 4 then blocksOf P L k.1 else 0, ?_, ?_⟩, ?_, ?_⟩
  · rintro g d t ins hg hσ ⟨hw, d', n, rfl, hs⟩ hat hi hc
    exact Wg0.w0_vote_tmpl d' hs t ins hat hi hc
  · rintro g d hg hσ ⟨hw, d', n, rfl, hs⟩
    exact w0_vote_rel hp hX hFw hub hg hw hσ hs
  · rintro g d hg hσ ⟨hw, d', n, rfl, hs⟩
    have := vote_cnt_lt hp hX hFw hub hw hg hσ hs
    have hk := (warp_key hp g).mp hw
    show _ < (if (warpKey L g).2 < 4 then _ else 0)
    simp only [hk, ↓reduceIte]
    exact this
  · intro g k pc d hg hσ hex
    by_cases hw : warpOf L g < 4
    · have := vote_cnt_exit hp hX hFw hub hw hg hσ hex
      show (if (warpKey L g).2 < 4 then _ else 0) ≤ _
      simp only [(warp_key hp g).mp hw, ↓reduceIte]
      exact this
    · simp [(warp_key hp g).not.mp hw]
  · intro h hpd hn
    have hs : SameWarp L h h := ⟨⟨hpd.1, hpd.1, rfl⟩, rfl⟩
    obtain ⟨A, ⟨C⟩, hAg, hall⟩ := cls_of hp hX hFw hub hpd.1
    exact (warpPair_of_cls hp hX hFw hub hgrp C hs hAg (hall _ hs)).dead hpd hn
  · rintro g h d hg hh hsw hσ ⟨hw, d', n, rfl, hs⟩ hle hnot hne
    have := vote_lag hp hX hFw hub hw hsw hσ hs hle hnot hne
    rwa [timed_eq] at this

/-- **A released pending lane at the vote steps** (pc 578): its state is the vote of
warpgroup 0 (`Followed`, the invariant, the role by pc). -/
theorem vote_steps_pend (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hs : SafeGoal kernel Assumptions.all L m) (hFw : Follow P L X)
    (hd : ∀ h, TensorStore.Drained drainSel X h) (hW : VoteRel P L m X)
    (hpd : Frame.Pending L X g) (hat : PendAtPc P L X g 578) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨σ, hσ, hi, hpc⟩ := pendAtPc_iff.1 hat
  have hF := follow_iff.mp hFw
  have hJ := (hF g hpd.1 (X.tr g).length).2 σ hσ
  have hV : VoteAt P L g σ := by
    have h := state_role hJ hi
    rw [hpc] at h
    cases h with
    | wg0 d n hR hw hs' _ =>
      exact ⟨hw, d, n, rfl, Wg0.site_vote_of_pc (by simpa using hs'.symm)⟩
    | _ => exfalso; omega
  have hlaunch := launched_all hX
  have hcl := noCanceled hX
  have ht : Frame.Tracked (thread P L) X := fun h k hh => (hF h hh k).1
  rw [timed_eq]
  exact Sched.warpVote_steps (fun hsw => warpKey_eq hsw) (fun _ _ => thread_sound hp) hs ht hW
    (fun l hl => by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hl)
    (by rw [hp.block]) hlaunch hcl (wf_appendLanes hX hd) (Sched.fault_extension hX hlaunch hc)
    hc.max hpd hσ hV

/-- **A released pending lane whose next event is at the vote steps.** -/
theorem vote_quiet_steps (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hs : SafeGoal kernel Assumptions.all L m) (hFw : Follow P L X)
    (hd : ∀ h, TensorStore.Drained drainSel X h) (hW : VoteRel P L m X)
    (hpd : Frame.Pending L X g) (hn : Sched.NextEv L kernel Assumptions.all m X g e)
    (hub : ∀ f, e.kind ≠ .ub f) (hk : e.pc = 578) : Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, -, hi, -, hpc⟩ := next_state hp hFw hn hub
  exact vote_steps_pend hp hc hs hFw hd hW hpd (pendAtPc_iff.2 ⟨σ, hσ, hi, hpc.symm.trans hk⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

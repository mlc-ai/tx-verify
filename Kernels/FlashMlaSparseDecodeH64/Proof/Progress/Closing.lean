-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingProgress
public import Lemmas.Step.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.CtaBarFinishExit
import Lemmas.Step.Issue

@[expose] public section

/-! # Issuing, releasing, and leaving the closing CTA barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def closingWarps : Finset Nat := Finset.range 12

private theorem closing_shape (hpre : Pre P L mem0) :
    NamedBar.Shape L none closingWarps 12 := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · rw [hpre.block]
    rfl
  · intro w hw
    rw [hpre.block]
    exact Finset.mem_range.mp hw

private theorem closing_sources (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) : NamedBar.Sources L X none closingWarps 12 := by
  rintro ⟨g, i⟩ tag count ⟨mode, he⟩ hg
  obtain ⟨_, _, _, hc, _⟩ := ScoreClosingGate.closing_at hpre hX hs ht he
  refine ⟨Finset.mem_range.mpr ?_, hc⟩
  change g % L.block / 32 < 12
  rw [hpre.block]
  have h := Nat.mod_lt g (by decide : 0 < 384)
  omega

private theorem wf_closing_records :
    Assumption.WfCtaHistory (L := L) (K := kernel) (mem0 := mem0) Assumptions.all := by
  intro Y c suffix hY
  exact Interface.all_wf_effects hY (Y.le_withCtaHistory c ⟨suffix, rfl⟩) rfl rfl rfl

/-- Once all CTA lanes have issued their closing arrivals, an extension of a maximal
execution with the same traces releases a lane waiting at that barrier. -/
theorem closing_released {tag : Nat} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hNoFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) 12 none tag)
    (hArrived : ∀ lane < L.block, ∃ i eventTag,
      X.IsBarrier (g / L.block * L.block + lane, i) 12 none eventTag) :
    ∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g := by
  apply NamedBar.sync_release_of_wf hmax wf_closing_records hNoFault (closing_shape hpre)
    (closing_sources hpre hmax.1 hs ht) (Frame.lt_of_get hmax.1 hlast) hlast
  intro lane hLane _
  obtain ⟨i, tag', he⟩ := hArrived lane hLane
  exact ⟨i, tag', .sync, he, (ScoreClosingGate.closing_ordinal hpre hmax.1 hs ht he).trans
    (ScoreClosingGate.closing_ordinal hpre hmax.1 hs ht hlast).symm⟩

/-- A released thread whose selected output stores have drained their shared reads cannot
remain at a return instruction in a maximal execution. -/
theorem return_not_pending (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hDrained : ∀ i, i.1 = g →
      TensorStore.Selected Assumptions.storeDrain.storeReadsBeforeExit X i →
      X.AsyncPresent i .readsDone)
    {d : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hsite : ClosingProgress.ReturnSite d) : False := by
  obtain ⟨t, t1, hrun, hlocal, he⟩ := ClosingProgress.return_event hmax.1 hs hub hp hd hsite
  have hNonempty := ClosingProgress.nonempty_tail hd (by
    rintro rfl
    exact hsite)
  exact hmax.not_grows (PTX.Step.plain_counted_extension hmax.1 hp.1 (.inl hNonempty) hrel
    hrun hlocal he trivial rfl (by intros; simp) (by intros; simp) (by intros; simp) rfl
    (hmax.1.tmemPairResult.snoc_not_wr (by intros; simp))
    (Interface.all_wf_snoc_of_not_nc hmax.1 (by intros; simp) (fun _ => hDrained)))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

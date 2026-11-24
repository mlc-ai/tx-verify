-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Completion
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcDrainTrace
import Lemmas.Protocol.NamedBarLedger

public section

/-! # The closing phase has drained the issued Tensor Core operations -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem output_stage_of_exit {g : Nat} (hwg : wgOf L g = 0) {i tag : Nat}
    (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    ∃ j e d, X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧ d.site = .oStage 0 0 := by
  have hg := Frame.lt_of_get hX he
  have hSound := (hs g hg).machine
  have hd := Wg0OutputVisits.doneAtExit hX hSound ht hwg he rfl
  obtain ⟨j, _, b, e, hb, hSite, he', _⟩ :=
    Wg0OutputVisits.barrierBeforeDone hpre hX hg hSound hwg hd 0
  obtain ⟨_, _, _, k, _, f, d, _, hf, hD, hStage, _, _, _, _⟩ :=
    Wg0OutputVisits.stagedBeforeBarrier hpre hX hg hSound hwg
      (PTX.len_of_get he') hb hSite 0 0
  exact ⟨k, f, d, hf, hD, hStage⟩

private theorem tc_completed_of_output_stage {g h k j : Nat} {e : Event} {d : Wg0.D}
    (hCta : ctaOf L h = ctaOf L g) (hOp : X.TcAsync (h, k)) (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hStage : d.site = .oStage 0 0) :
    X.async.mmaDone (h, k) = true := by
  obtain ⟨issuer, hmma⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
    (fun g hg => (hs g hg).machine)
  obtain ⟨q, hQ, hSite | hSite⟩ := TcDrainTrace.async_site hpre hX hs ht hOp
  · obtain ⟨copy, hCopy⟩ := hSite
    obtain ⟨w, wt, c, ct, _, sp, rank, p, _, hw, hCommit, _, _, hPV, _,
        hp, hObs, _⟩ :=
      StageAfterPv.final_commit_before_stage hpre hX hs ht hmma he hd hStage
    have hSame := hmma h k q hCta hQ (by simp [hCopy])
    obtain ⟨f, hf⟩ : ∃ f, X.get (h, k) = some f := by
      rcases hOp with ⟨_, _, _, _, _, hGet⟩ | ⟨_, _, hGet⟩ | ⟨_, _, hGet⟩
      all_goals exact ⟨_, hGet⟩
    have hBefore : k < c := by
      rw [hSame] at hf hQ
      exact TcDrainTrace.copy_before_pv_commit hpre hX hs hf hQ hp hCopy hPV
    obtain ⟨hNotified, _⟩ := hObs.waitObserves_tcNotify hw
    exact (hX.tcCommit (issuer, c) rank hNotified).2 (h, k)
      ⟨hSame, hBefore, hOp, sp, ct, hCommit⟩
  · exact (StageAfterPv.operand_completed (index := 0) (isB := false)
      hpre hX hs ht hmma hCta hOp hQ hSite he hd hStage).1
end

variable (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hsafe : ∀ Y, Consistent L kernel Assumptions.all mem0 Y →
      ¬ Unsafe L kernel Assumptions.all mem0 Y)
    (hArrived : ∀ cta < L.grid, ∀ lane < L.block, ∃ i tag,
      X.get (cta * L.block + lane, i) = some ⟨tag, .bar 12 none .sync⟩)
include hpre hmax hs ht hsafe hArrived

/-- The successful final PV acquire covers each issued async operation of that CTA, once its
actual closing arrivals have all been recorded. -/
theorem tc_drained_of_closing {i : EvId} (hi : X.TcAsync i) : X.async.mmaDone i = true := by
  obtain ⟨g, k⟩ := i
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := by
    rcases hi with ⟨_, _, _, _, _, hGet⟩ | ⟨_, _, hGet⟩ | ⟨_, _, hGet⟩
    all_goals exact ⟨_, hGet⟩
  have hb : 0 < L.block := by rw [hpre.block]; decide
  let cta := ctaOf L g
  let base := cta * L.block
  have hcta : cta < L.grid := PTX.NamedBar.cta_lt (Frame.lt_of_get hmax.1 he)
  obtain ⟨i, tag, hExit⟩ := cta_exited_of_arrived hpre hmax hs ht hsafe hcta
    (hArrived cta hcta) 0 hb
  have he : X.get (base, i) = some ⟨tag, .exit⟩ := by simpa only [base, Nat.add_zero] using hExit
  have hwg : wgOf L base = 0 := by
    unfold wgOf
    rw [tidOf_eq hpre, ← hpre.block]
    simp [base]
  obtain ⟨j, staged, d, hStage, hD, hSite⟩ := output_stage_of_exit hpre hmax.1 hs ht hwg he
  have hCta : ctaOf L g = ctaOf L base := by
    change cta = (cta * L.block) / L.block
    exact (Nat.mul_div_cancel _ hb).symm
  exact tc_completed_of_output_stage hpre hmax.1 hs ht hCta hi hStage hD hSite

/-- Actual CTA-wide closing arrivals suffice to finish kernel progress, once tracking and
safety hold. -/
theorem complete_of_all_closing_arrivals :
    Complete L X :=
  complete_of_closing_and_tc hpre hmax hs ht hsafe hArrived
    (fun _ hi => tc_drained_of_closing hpre hmax hs ht hsafe hArrived hi)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

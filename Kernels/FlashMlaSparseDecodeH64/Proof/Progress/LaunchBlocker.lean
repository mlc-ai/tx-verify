-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.WaitOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressCta
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGateRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution

public section

/-! # Missing participants at the initial CTA gate -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem prologue_before_handoff {g h : Nat} {s : Site} {w : Fin 3}
    (hn : ∀ k, s ≠ .handoff k) :
    priority P L h (.prologue s) < priority P L g (.prologue (.handoff w)) := by
  cases s
  case' handoff k => exact (hn k rfl).elim
  all_goals simp only [priority, prologueRank]
  all_goals omega

/-- A lane at the actual launch gate either releases with the same traces or identifies a missing
CTA participant in an earlier prologue state. -/
theorem bar0_release_or_earlier (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hNoFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    {g tag : Nat} (he : X.IsBarrier (g, (X.tr g).length - 1) 0 none tag) :
    ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d) ∧
      ((∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g) ∨
        ∃ other q, SameCta L g other ∧ Frame.Pending L X other ∧
          Frame.stateAt (Machine.code P L) X other (X.tr other).length = some (some q) ∧
          priority P L other q < priority P L g d) := by
  have hg := Frame.lt_of_get hmax.1 he
  have hLen : (X.tr g).length - 1 < (X.tr g).length := PTX.len_of_get he
  have hIndex : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
  obtain ⟨hOrdinal, w, hState⟩ := MachineTracking.launch_arrival hmax.1 hs ht he
  rw [hIndex] at hState
  refine ⟨.prologue (.handoff w), hState, ?_⟩
  classical
  by_cases hall : ∀ lane < L.block, ∃ i eventTag,
      X.IsBarrier (g / L.block * L.block + lane, i) 0 none eventTag
  · apply Or.inl
    refine release_launch_gate hpre hmax hs ht hNoFault hg ⟨_, he, rfl⟩ ?_
    intro lane hLane
    obtain ⟨i, t, hEvent⟩ := hall lane hLane
    exact ⟨i, _, hEvent, rfl, (MachineTracking.launch_arrival hmax.1 hs ht hEvent).1.trans
      hOrdinal.symm⟩
  push Not at hall
  obtain ⟨lane, hLane, hMissing⟩ := hall
  let other := g / L.block * L.block + lane
  have hOther := PTX.NamedBar.cta_thread_lt (PTX.NamedBar.cta_lt hg) hLane
  have hGeo : other / L.block = g / L.block := by
    change (g / L.block * L.block + lane) / L.block = g / L.block
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hLane),
      Nat.div_eq_of_lt hLane, Nat.zero_add]
  have hSame : SameCta L g other := ⟨hg, hOther, hGeo.symm⟩
  have hp : Frame.Pending L X other := by
    refine ⟨hOther, ?_, ?_⟩
    · rintro ⟨_, _, hc⟩
      obtain ⟨i, s, tg, _, hIssue, _⟩ := hmax.1.clc.canceled_has_issue hc
      exact GlobalWrites.no_clc (i := i) (s := s) (tg := tg) hmax.1 hIssue
    · intro et hLast
      have hExit : X.get (other, (X.tr other).length - 1) = some ⟨et, .exit⟩ := by
        change (X.tr other)[(X.tr other).length - 1]? = _
        rwa [← List.getLast?_eq_getElem?]
      obtain ⟨j, _, hj, _⟩ :=
        MachineTracking.exit_follows_gate hpre hmax.1 (fun g hg => (hs g hg).machine) hExit
      exact hMissing j _ hj
  obtain ⟨d, hd⟩ := hLive other hp
  obtain ⟨s, rfl, hn⟩ := MachineTracking.state_before_gate_of_missing hmax.1 hOther
    (hs other hOther).machine hd hMissing
  exact .inr ⟨other, .prologue s, hSame, hp, hd, prologue_before_handoff hn⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

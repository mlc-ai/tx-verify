-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LaunchBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.NamedBarrier
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.PairBarrier
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.NamedBarChecks
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NamedBarTrace
import Lemmas.Clc.ClcExecution

public section

/-! # Pending lanes at all CTA and named-barrier waits -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Each pending lane at a barrier descends to an earlier state. Completing a barrier record
with the same traces allows the released-site argument in that maximal execution. -/
theorem pending_barrier_earlier {g tag id : Nat} {count : Option Nat} {mode : BarMode}
    {d : Machine.ThreadD} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (htrack : ∀ Y, Consistent L kernel Assumptions.all mem0 Y →
      Frame.Tracked (Machine.code P L) Y)
    (hp : PendingState P L X g d)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨tag, .bar id count mode⟩) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
  have hX := hmax.1
  have ht := htrack X hX
  have hub := Safety.no_ub hpre hX hs ht
  have hLive : ∀ h, Frame.Pending L X h →
      ∃ z, Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some z) :=
    fun _ h => pending_followed hpre hX hs ht h
  have hFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y :=
    fun Y hY => Safety.no_ctaBarFault hpre hY hs (htrack Y hY)
  have handle {d' : Machine.ThreadD}
      (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d'))
      (hResult :
        (∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g) ∨
        ∃ h q, SameCta L g h ∧ Frame.Pending L X h ∧
          Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some q) ∧
          priority P L h q < priority P L g d') :
      ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
    have hEq := Option.some.inj (Option.some.inj (hState.symm.trans hp.2))
    subst d'
    rcases hResult with ⟨Y, hMaxY, hEq, hRel⟩ | ⟨h, q, _, hP, hState, hLt⟩
    · have transfer (h : Nat) (q : Machine.ThreadD) :
          PendingState P L Y h q ↔ PendingState P L X h q := by
        have hXNo : ¬ ClcCanceled L X h := by
          rintro ⟨_, _, hCanceled⟩
          obtain ⟨i, sp, tg, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
          exact GlobalWrites.no_clc (i := i) (s := sp) (tg := tg) hX hi
        have hYNo : ¬ ClcCanceled L Y h := by
          rintro ⟨_, _, hCanceled⟩
          obtain ⟨i, sp, tg, _, hi, _⟩ := hMaxY.1.clc.canceled_has_issue hCanceled
          exact GlobalWrites.no_clc (i := i) (s := sp) (tg := tg) hMaxY.1 hi
        simp only [PendingState, Frame.Pending, Frame.stateAt, hEq, hXNo, hYNo]
      obtain ⟨h, q, hP, hLt⟩ := pending_released_earlier hpre hMaxY hs (htrack Y hMaxY.1)
        ((transfer g d).mpr hp) hRel
      exact ⟨h, q, (transfer h q).mp hP, hLt⟩
    · exact ⟨h, q, ⟨hP, hState⟩, hLt⟩
  rcases NamedBarTrace.gate_operands hpre hX hs ht he with h0 | h9 | ⟨p, hp⟩ | h12
  · obtain ⟨_, hD, hResult⟩ := bar0_release_or_earlier hpre hmax hs ht hFault hLive h0
    exact handle hD hResult
  · obtain ⟨_, hD, hResult⟩ := bar9_release_or_earlier hpre hmax hs ht hub hFault hLive h9
    exact handle hD hResult
  · obtain ⟨_, hD, hResult⟩ := pair_release_or_earlier hpre hmax hs ht hub hFault hLive hp
    exact handle hD hResult
  · obtain ⟨_, hD, hResult⟩ := bar12_release_or_earlier hpre hmax hs ht hub hFault hLive h12
    exact handle hD hResult

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.WaitOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Lemmas.Kernel.ProgressDescent

public section

/-! # Closing arrivals from pending-thread descent -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- An actual closing arrival from each lane of every launched CTA. -/
@[expose] def AllClosingArrived (L : Launch) (X : Execution) : Prop :=
  ∀ cta < L.grid, ∀ lane < L.block, ∃ i tag,
    X.get (cta * L.block + lane, i) = some ⟨tag, .bar 12 none .sync⟩

/-- A launched pending thread together with its machine's state at the trace tail. -/
@[expose] def PendingState (P : Params) (L : Launch) (X : Execution)
    (g : Nat) (d : Machine.ThreadD) : Prop :=
  Frame.Pending L X g ∧ Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d)

/-- If every pending state leads to an earlier pending state, all lanes have arrived to close. -/
theorem closing_arrivals_of_descent {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hDescend : ∀ g d, PendingState P L X g d →
      ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d) :
    AllClosingArrived L X := by
  have hNoPending := PTX.Proof.ProgressDescent.not_of_descent
    (p := fun pair : Nat × Machine.ThreadD => PendingState P L X pair.1 pair.2)
    (fun pair => priority P L pair.1 pair.2)
    (fun (g, d) hp => by
      obtain ⟨h, q, hTail, hLt⟩ := hDescend g d hp
      exact ⟨(h, q), hTail, hLt⟩)
  intro cta hc lane hl
  let g := cta * L.block + lane
  have hg : g < L.threads := by
    have hspan := Nat.mul_le_mul_right L.block (Nat.succ_le_of_lt hc)
    rw [Nat.succ_mul] at hspan
    change cta * L.block + lane < L.grid * L.block
    omega
  by_cases hExit : ∃ tag, (X.tr g).getLast? = some ⟨tag, .exit⟩
  · obtain ⟨tag, hLast⟩ := hExit
    rw [List.getLast?_eq_getElem?] at hLast
    obtain ⟨i, _, tag', he⟩ := ClosingOrder.arrival_before_exit hpre hX hs ht hLast
    exact ⟨i, tag', he⟩
  · have hp : Frame.Pending L X g := by
      refine ⟨hg, ?_, fun tag he => hExit ⟨tag, he⟩⟩
      rintro ⟨_, _, hCanceled⟩
      obtain ⟨i, sp, targets, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
      exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hi
    obtain ⟨d, hd⟩ := pending_followed hpre hX hs ht hp
    exact (hNoPending (g, d) ⟨hp, hd⟩).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerExit
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # An exit event is fired from an exit stage

A thread's exit event is fired by the exit instruction, which only an exit stage of the thread's
machine reaches; so the state the exit event fires from has an exit offset (`ThreadD.exitOff`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An exit event is fired from an exit stage of its thread. -/
theorem exit_stage_of_exit (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k pc : Nat} {d : ThreadD} (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) : d.exitOff ≠ none := by
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hp := ret_pc hc (fires_exit_op hfire rfl)
  rcases d with p | (l | m | sd | cs)
  · exfalso
    obtain ⟨site, w⟩ := p
    change site.pc ∈ Flow.exit.toList at hp
    cases site <;> simp only [Prologue.Site.pc] at hp <;> clear * - hp <;> revert hp <;>
      decide +revert
  · obtain ⟨site, mm, n, q, cp, r, x⟩ := l
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp; revert hp; simp only [Loader.Site.pc];
                                    decide +revert)
    subst hsite
    simp [ThreadD.exitOff, Loader.exitOff]
  · obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp; revert hp; simp only [Mma.Site.pc];
                                    decide +revert)
    subst hsite
    simp [ThreadD.exitOff, Mma.exitOff]
  · obtain ⟨site, ap, cp, r, x⟩ := sd
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp; revert hp; simp only [Scheduler.Site.pc];
                                    decide +revert)
    subst hsite
    simp [ThreadD.exitOff, Scheduler.exitOff]
  · obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := cs
    have hsite : site = .exit := by
      change site.pc ∈ Flow.exit.toList at hp
      cases site <;> first | rfl | (exfalso; clear * - hp; revert hp; simp only [Consumer.Site.pc];
                                    decide +revert)
    subst hsite
    simp [ThreadD.exitOff, Consumer.exitOff]

/-- An exit event is fired from a thread state, which is one of the thread's exit stages. -/
theorem exit_event_state' (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k pc : Nat} (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ d : ThreadD, Frame.stateAt (code L) X g k = some (some d) ∧ d.exitOff ≠ none := by
  rcases (Frame.trace (fun _ => sound hpre) hX hg).fired he with ⟨τ, -, ha, -⟩ | ⟨-, hub⟩
  · cases τ with
    | none => exact absurd ha (tracked hpre hX g k hg)
    | some d => exact ⟨d, ha, exit_stage_of_exit hpre hX he ha⟩
  · obtain ⟨pc', f, hf⟩ := hub
    cases hf

end
end PTX.Kernels.Fp16Gemm8192.Proof

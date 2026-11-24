-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaTracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Flow.Next

public section

/-! # Continuations of returned MMA role events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbMma

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every actual returned event of the MMA role preserves the represented thread. -/
theorem next_live (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) : UbRoles.MmaContinues P L X := by
  intro g i d e he hd hReturns
  by_cases hEntry : d.site = .elect ∨ d.site = .loadTopk ∨ d.site = .loadExtra
  · obtain ⟨_, hNext⟩ := MmaTracking.entry_next hpre hX hs he hd hEntry hReturns
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hNext] at hn
    change _ = Machine.next P L g (.mma d) e at hn
    rw [← hn]
    exact Option.some_ne_none _
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hFired⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  cases h : d.site
  case head =>
    obtain ⟨t, ins, o, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    change kernel.code[d.site.pc]? = some ins at hc
    rw [h] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
    cases o with
    | none => exact (hReturns (fires_none_ends hf)).elim
    | some u =>
      obtain ⟨_, _, _, recv, _, hk, _⟩ := fires_shfl (d := 558) (p := some 10) hf
      rw [hk]
      by_cases hv : recv = PTX.Proof.b32 (warpOf L g) <;>
        simp [Machine.next, Wg1Mma.next, h, hv]
  case elect => exact (hEntry (.inl h)).elim
  case loadTopk => exact (hEntry (.inr (.inl h))).elim
  case loadExtra => exact (hEntry (.inr (.inr h))).elim
  case qWait =>
    obtain ⟨_, _, _, _, hk⟩ := RingEvents.mma_wait_object hpre (.inl h) hFired
    simp [Machine.next, Wg1Mma.next, h, hk]
  case qCopyWait =>
    obtain ⟨_, _, _, _, hk⟩ := RingEvents.mma_wait_object hpre (.inr (.inl h)) hFired
    simp [Machine.next, Wg1Mma.next, h, hk]
  case kvWait =>
    obtain ⟨_, _, _, _, hk⟩ := RingEvents.mma_wait_object hpre (.inr (.inr (.inl h))) hFired
    simp [Machine.next, Wg1Mma.next, h, hk]
  case soWait =>
    obtain ⟨_, _, _, _, hk⟩ := RingEvents.mma_wait_object hpre (.inr (.inr (.inr h))) hFired
    simp [Machine.next, Wg1Mma.next, h, hk]
  case pvCommit =>
    by_cases hi : d.i + 1 < Wg1Mma.blocks P L g <;> simp [Machine.next, Wg1Mma.next, h, hi]
  all_goals simp [Machine.next, Wg1Mma.next, h]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbMma

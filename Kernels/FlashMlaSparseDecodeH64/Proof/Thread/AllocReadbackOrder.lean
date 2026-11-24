-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.InitCtaPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RoleSharedWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds

@[expose] public section

/-! # Actual sources of an allocation read-back in a followed execution -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g j : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- No tensor load reaches the allocation word. Ordinary role writes in the same CTA follow
its prologue read-back, so no byte can read from one of them. -/
theorem sources_in_prologue (he : X.get (g, j) = some e)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead))) :
    ReadbackSourcesInPrologue P L X (g, j) := by
  unfold ReadbackSourcesInPrologue
  intro b hb w hr
  obtain ⟨bytes, hread⟩ := readback_access hpre hX hs he hq
  have hsrc := (hX.rf _ _ _ hread).2 b hb
  rw [hr] at hsrc
  obtain ⟨a, bs, hw, hcover, _⟩ := hsrc
  rcases Wg2.raw_read_competing_kinds hX hw hcover rfl with
    ⟨i, rfl, hwrite⟩ | ⟨i, x, y, k, rfl⟩
  · obtain ⟨site, hget⟩ := hwrite
    obtain ⟨d, hd⟩ := Frame.event_state hs hX ht hget (by simp)
    by_cases hIsPrologue : ∃ s, d = .prologue s
    · obtain ⟨s, rfl⟩ := hIsPrologue
      exact ⟨s, hd⟩
    have hrole : ∀ s, d ≠ .prologue s := fun s h => hIsPrologue ⟨s, h⟩
    have hspace : a.loc.space = .shared := hcover.1.symm
    have hown := RoleSharedWrites.shared_cta_of_state hpre hs hX hget hd hspace
    have hcta : ctaOf L g = ctaOf L i.1 := hcover.2.1.trans hown
    have hAfter := InitCtaPublication.alloc_read_before_role hpre hX
      (fun h hh => (hs h hh).machine) ht he hget hq hd hrole hcta
    exact (hX.noFuture _ _ _ _ _ hread hb hr (.direct (.inl hAfter))).elim
  · have hbound := (TensorSharedBounds.written_byte_windows hpre hX hs ht hw hcover).2.2.2
    change L.sharedBase + 222752 + b < L.sharedBase + 222752 at hbound
    omega

/-- An allocation read in a followed execution with safe Tensor Memory resources obtains
the zero column and reaches relinquishment. -/
theorem readback_relinquishes (hsafe : ¬ Tmem.Pair.ResourceUnsafe L X) (he : X.get (g, j) = some e)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead))) :
    Frame.stateAt (Machine.code P L) X g (j + 1) = some (some (.prologue .relinquish)) :=
  follows_read_of_prologue_sources hpre hX hs (sources_in_prologue hpre hX hs ht he hq) hsafe he hq

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation

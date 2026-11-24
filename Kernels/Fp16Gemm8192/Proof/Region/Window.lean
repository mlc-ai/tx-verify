-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Region.Accessors

@[expose] public section

/-! # The shared window of a launched CTA

An access covering a shared byte is in the window of a launched CTA (`access_cta`): a thread's
access is in its own CTA's window, a tensor load writes and a tensor store reads its issuer's CTA,
an MMA reads one of the CTA pair of its leader CTA, a cancellation response is written to a target
of its request. With the regions of the window (`regions`), every shared access is in one of them
(`sharedWindow`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

namespace Region

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A launched thread's CTA is launched. -/
theorem cta_lt (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) : g / L.block < L.grid :=
  (Nat.div_lt_iff_lt_mul (by rw [hpre.block]; decide)).mpr hg

/-- **A shared byte an access covers is in a launched CTA.** -/
theorem access_cta (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {ref : Ref} {a : Acc} {w : Bool} {l : Loc} (h : X.Intent ref a w)
    (hc : a.Covers l) (hs : l.space = .shared) : l.cta < L.grid := by
  have hgrid := hpre.grid
  obtain ⟨hsp, hct, hlo, hhi⟩ := hc
  rcases Execution.shared_intent h ⟨hsp, hct, hlo, hhi⟩ hs with
    ⟨⟨g, k⟩, rfl, hacc⟩ | ⟨i, isB, idx, rfl⟩ | ⟨⟨gi, ki⟩, x, y, kk, rfl⟩ | ⟨i, x, y, kk, rfl⟩ |
    ⟨⟨gi, ki⟩, c, s, tg, rfl, hi, hm, rfl⟩ | ⟨i, q, sc, rfl, hcopy⟩ | ⟨i, rfl, hpf⟩
  · rcases hacc with ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨old, new, pc, hget⟩
    · have hg := Frame.lt_of_get hX hget
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      rcases (ht.access_region hg hget hσ).1 a bs rfl with ⟨hl, -⟩ | ⟨hl, -⟩ <;>
        rw [hct, hl] <;> exact cta_lt hpre hg
    · have hg := Frame.lt_of_get hX hget
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      rcases (ht.access_region hg hget hσ).2.1 a bs rfl with ⟨c, rfl⟩ | ⟨hl, -⟩
      · obtain ⟨-, hst, -⟩ := ht.cons_out hg hget hσ
        obtain ⟨s0, i0, el0, -, hl, -⟩ := hst a bs rfl
        rw [hct, hl]
        exact cta_lt hpre hg
      · rw [hct, hl]
        exact cta_lt hpre hg
    · exact (Safety.no_rmw hX ht hget).elim
  · obtain ⟨dst, sp, acc, mask, s0, jj, b0, hi, -, h2, -, hidx, hl, -⟩ :=
      InputRing.read_at hpre ht hX ⟨a, w, h, ⟨hsp, hct, hlo, hhi⟩⟩
    obtain ⟨pc, hget⟩ := hi
    have hg := cta_lt hpre (Frame.lt_of_get hX hget)
    rw [hl]
    simp only [InputRing.stageByte]
    have : idx / 32 / 128 < 2 := by omega
    omega
  · obtain ⟨-, sp, addr, ⟨pc, hget⟩, -, -⟩ := id h
    have hg := Frame.lt_of_get hX hget
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨c, rfl⟩ := (ht.access_region hg hget hσ).2.2 addr sp rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hl, -⟩ :=
      OutputRing.tma_info hX ht hσ h ⟨hsp, hct, hlo, hhi⟩
    rw [hl]
    exact cta_lt hpre hg
  · obtain ⟨pc, a0, sp, s0, j0, hget, -, -, -, -, hl, -⟩ :=
      InputRing.write_at ht hX ⟨a, w, h, ⟨hsp, hct, hlo, hhi⟩⟩
    rw [hl]
    exact cta_lt hpre (Frame.lt_of_get hX hget)
  · rw [hct]
    exact ((hX.clc.2.2.2.1 _ s tg hi).2.2 c).mp hm |>.2.2.2.2.2.2.1
  · exact (Safety.no_copy hX ht hcopy).elim
  · exact (Safety.no_bulkPrefetch hX ht hpf).elim

/-- **The shared window.** Every access of a shared byte is in a launched CTA's window, in one of
its regions. -/
theorem sharedWindow (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : SharedWindow L X := by
  intro ref a w l h hc hs
  refine ⟨access_cta hpre hX ht h hc hs, ?_⟩
  rcases regions hpre hX ht h hc hs with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact .inr (.inr (.inl h'))
  · exact .inr (.inr (.inr h'))
  · exact .inr (.inl h')
  · exact .inl h'

end Region

end

end PTX.Kernels.Fp16Gemm8192.Proof

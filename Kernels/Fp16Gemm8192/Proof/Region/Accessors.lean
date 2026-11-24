-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.Region
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Sources
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Safe
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds

@[expose] public section

/-! # The accessors of the kernel's shared memory regions

Every access covering a byte of a CTA's shared window lies in one region of the window, and is one
of the region's accessors (`regions`):

* the input stages (`IsInputStage`): the tensor loads write them, the MMAs read them as operands
  (`InputRing.write_at`, `InputRing.read_at`);
* the staging buffers (`IsStaging`): the consumers' staging stores write them, their TMA stores
  read them (`OutputRing.store_info`, `OutputRing.tma_info`);
* the CLC response buffer (`IsResponse`): the cancellation requests targeting the CTA write it, the
  threads read it (the request's response address, `RingEvent.clc`);
* the Tensor Memory base word (`IsBase`): the allocation writes it, a consumer reads it back.

A thread's own accesses are placed by the state it fires from (`ThreadFacts.access_region`), an
asynchronous operation's by its issuing event; no bulk copy is issued (`RingEvent.bulk`). The three
accessor premises follow: only tensor loads and MMA reads access the input stages
(`inputAccessors`), only consumer stores and TMA store reads the staging buffers
(`stagingAccessors`), and only cancellation responses targeting a CTA write its response buffer
(`responseWriters`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

namespace Region

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A staging byte of a consumer of the first two warp groups. -/
theorem staging_of {l : Loc} {t b : Nat} (hs : l.space = .shared) (ht : t < 256) (hb : b < 2)
    (hlo : L.sharedBase + Consumer.stagingBase t b ≤ l.addr)
    (hhi : l.addr < L.sharedBase + Consumer.stagingBase t b + 8192) : IsStaging L l := by
  simp only [Consumer.stagingBase] at hlo hhi
  have : t / 32 / 4 < 2 := by omega
  exact ⟨hs, by omega, by omega⟩

/-- **The regions of the shared window and their accessors.** An access covering a shared byte is
a tensor load's write or an MMA read of an input stage byte, a consumer's staging store or TMA
store read of a staging byte, a thread's read or a cancellation response's write of a response
buffer byte (of a request targeting the byte's CTA), or a thread's access of a base word byte. -/
theorem regions (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {ref : Ref} {a : Acc} {w : Bool} {l : Loc} (h : X.Intent ref a w) (hc : a.Covers l)
    (hs : l.space = .shared) :
    (IsInputStage L l ∧ ((∃ i x y k, ref = .async i (.write (.load x y k))) ∨
      ∃ i isB idx, ref = .async i (.mmaRead isB idx))) ∨
    (IsStaging L l ∧ ((∃ e pc bs c, ref = .thread e ∧ X.get e = some ⟨pc, .wr a bs⟩ ∧
        Frame.stateAt (code L) X e.1 e.2 = some (some (.inr (.cons c)))) ∨
      ∃ i x y k c, ref = .async i (.read (.store x y k)) ∧
        Frame.stateAt (code L) X i.1 i.2 = some (some (.inr (.cons c))))) ∨
    (IsResponse L l ∧ ((∃ e, ref = .thread e ∧ w = false) ∨
      ∃ i s tg, ref = .async i (.write (.cta l.cta)) ∧ X.ClcIssue i s tg ∧ l.cta ∈ tg)) ∨
    (IsBase L l ∧ ∃ e, ref = .thread e) := by
  obtain ⟨hsp, hct, hlo, hhi⟩ := hc
  rcases Execution.shared_intent h ⟨hsp, hct, hlo, hhi⟩ hs with
    ⟨⟨g, k⟩, rfl, hacc⟩ | ⟨i, isB, idx, rfl⟩ | ⟨⟨gi, ki⟩, x, y, kk, rfl⟩ | ⟨i, x, y, kk, rfl⟩ |
    ⟨⟨gi, ki⟩, c, s, tg, rfl, hi, hm, rfl⟩ | ⟨i, q, sc, rfl, hcopy⟩ | ⟨i, rfl, hpf⟩
  · -- A thread's access.
    rcases hacc with ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨bs, ⟨pc, hget⟩, rfl⟩ | ⟨old, new, pc, hget⟩
    · have hg := Frame.lt_of_get hX hget
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      rcases (ht.access_region hg hget hσ).1 a bs rfl with ⟨hl, hz⟩ | ⟨hl, hz⟩
      · simp only [hl, hz] at hlo hhi
        exact .inr (.inr (.inl ⟨⟨hs, hlo, by omega⟩, .inl ⟨_, rfl, rfl⟩⟩))
      · simp only [hl, hz] at hlo hhi
        exact .inr (.inr (.inr ⟨⟨hs, hlo, hhi⟩, _, rfl⟩))
    · have hg := Frame.lt_of_get hX hget
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
      rcases (ht.access_region hg hget hσ).2.1 a bs rfl with ⟨c, rfl⟩ | ⟨hl, hz⟩
      · obtain ⟨kk, i, el, -, -, -, htid, h1, h2⟩ :=
          OutputRing.store_info hX ht hget hσ ⟨hsp, hct, hlo, hhi⟩
        have hb := OutputRing.stagingOff_bounds (t := Consumer.tidOf L g) (b := kk.val % 2)
          i.isLt el.isLt
        refine .inr (.inl ⟨staging_of (b := kk.val % 2) hs htid (Nat.mod_lt _ (by decide))
          (by omega) (by omega), .inl ⟨_, pc, bs, c, rfl, hget, hσ⟩⟩)
      · simp only [hl, hz] at hlo hhi
        exact .inr (.inr (.inr ⟨⟨hs, hlo, hhi⟩, _, rfl⟩))
    · exact (Safety.no_rmw hX ht hget).elim
  · -- An MMA operand read.
    obtain ⟨-, -, -, -, s, jj, b, -, -, -, -, -, hl, -⟩ :=
      InputRing.read_at hpre ht hX ⟨a, w, h, ⟨hsp, hct, hlo, hhi⟩⟩
    refine .inl ⟨?_, .inr ⟨i, isB, idx, rfl⟩⟩
    rw [hl]
    have hb := b.isLt
    have hj := jj.isLt
    exact InputRing.stageByte_input s.isLt (by split <;> omega) (by omega)
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  · -- A tensor store's read.
    obtain ⟨-, sp, addr, ⟨pc, hget⟩, -, -⟩ := id h
    have hg := Frame.lt_of_get hX hget
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨c, rfl⟩ := (ht.access_region hg hget hσ).2.2 addr sp rfl
    obtain ⟨-, -, -, -, st, -, -, -, -, -, -, htid, h1, h2, -⟩ :=
      OutputRing.tma_info hX ht hσ h ⟨hsp, hct, hlo, hhi⟩
    exact .inr (.inl ⟨staging_of (b := st.val % 2) hs htid (Nat.mod_lt _ (by decide)) h1 h2,
      .inr ⟨(gi, ki), x, y, kk, c, rfl, hσ⟩⟩)
  · -- A tensor load's write.
    obtain ⟨-, -, -, s, j, -, -, hx, hy, hz, hl, -⟩ :=
      InputRing.write_at ht hX ⟨a, w, h, ⟨hsp, hct, hlo, hhi⟩⟩
    rw [hl]
    exact .inl ⟨InputRing.stageByte_input s.isLt j.isLt hx hy hz, .inl ⟨i, x, y, kk, rfl⟩⟩
  · -- A cancellation response's write.
    obtain ⟨pc, hget⟩ := hi
    have hg := Frame.lt_of_get hX hget
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨⟨rg, sl, f⟩, -, hby, -, hresp, -⟩ := (ht.ring_event hg hget hσ).clc s tg rfl
    have hoff : Bar.responseOff ⟨rg, sl, f⟩ = 144 := by
      cases rg <;> cases f <;> simp only [Bar.clcBy] at hby
      rfl
    simp only [hresp, hoff] at hlo hhi hct
    subst hct
    exact .inr (.inr (.inl ⟨⟨hs, hlo, by omega⟩, .inr ⟨(gi, ki), s, tg, rfl, ⟨pc, hget⟩, hm⟩⟩))
  · -- No linear copy and no bulk prefetch is issued.
    exact (Safety.no_copy hX ht hcopy).elim
  · exact (Safety.no_bulkPrefetch hX ht hpf).elim

/-- **Only tensor loads write the input stages and only MMA operand reads read them.** -/
theorem inputAccessors (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : InputAccessors L X := by
  intro ref a w l h hc hl
  rcases regions hpre hX ht h hc hl.1 with ⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact h'
  all_goals (exfalso; obtain ⟨-, h1, h2⟩ := hl; obtain ⟨-, h3, h4⟩ := h'; omega)

/-- **Only consumer staging stores and TMA store reads access the staging buffers.** -/
theorem stagingAccessors (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : StagingAccessors L X := by
  intro ref a w l h hc hl
  rcases regions hpre hX ht h hc hl.1 with ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exfalso; obtain ⟨-, h1, h2⟩ := hl; obtain ⟨-, h3, h4⟩ := h'; omega
  · exact h'
  all_goals (exfalso; obtain ⟨-, h1, h2⟩ := hl; obtain ⟨-, h3, h4⟩ := h'; omega)

/-- **Only cancellation responses targeting a CTA write its response buffer.** -/
theorem responseWriters (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ResponseWriters L X := by
  intro cta k hk w a bs hw hc
  rcases regions hpre hX ht (Execution.MemWrites.intent hw) hc rfl with
    ⟨⟨-, h1, -⟩, -⟩ | ⟨⟨-, h1, -⟩, -⟩ | ⟨-, ⟨-, -, hf⟩ | ⟨i, s, tg, rfl, hi, hm⟩⟩ | ⟨⟨-, -, h2⟩, -⟩
  · simp only at h1; omega
  · simp only at h1; omega
  · cases hf
  · exact ⟨i, s, tg, rfl, hi, hm⟩
  · simp only at h2; omega

end Region

end

end PTX.Kernels.Fp16Gemm8192.Proof

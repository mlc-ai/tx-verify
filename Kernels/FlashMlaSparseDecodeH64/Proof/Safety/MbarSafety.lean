-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarSimpleFaults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingPhases
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarByteIsolation
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarIndexFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarLastStoreFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarQueryFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarQueryLoadFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarRawFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarRawReadyFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarUnitFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.StaticFaults

public section

/-! # Safety of the barrier object histories -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow AsyncCopy MBarrier Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
include hpre hX hs

/-- Every record other than an initialization belongs to a named barrier of a launched CTA. -/
theorem mbar_slot_of_noninit (ht : Frame.Tracked (Machine.code P L) X) {m : Loc} {r : Record Ref}
    (hr : r ∈ X.objects m) (hn : ∀ n, r.action ≠ .init n) :
    ∃ cta < L.grid, ∃ mb : Protocol.Mbar, m = mb.loc L cta := by
  rcases mbar_record_published hpre hX hs ht hr with ⟨⟨n, hAct⟩, _⟩ | ⟨i, _, hInit, _⟩
  · exact (hn n hAct).elim
  obtain ⟨g, k⟩ := i
  obtain ⟨e, he⟩ := hInit
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, _, hLoc, _⟩ :=
    RingInitSources.init_from_trace hpre hX (hs g hg).machine ht he rfl
  have hOffsets : ∀ j : Fin 23, initOff j ∈ Protocol.Mbar.all.map Protocol.Mbar.off := by
    decide +kernel
  obtain ⟨mb, _, hoff⟩ := List.mem_map.mp (hOffsets j)
  refine ⟨ctaOf L g, NamedBar.cta_lt hg, mb, ?_⟩
  rw [hLoc]
  change (⟨.shared, ctaOf L g, L.sharedBase + initOff j⟩ : Loc) =
    ⟨.shared, ctaOf L g, L.sharedBase + mb.off⟩
  rw [hoff]

/-- Record faults are the only remaining part of the TMA check after publication and isolation. -/
theorem tmaUnsafe_iff_record_fault (ht : Frame.Tracked (Machine.code P L) X) :
    TmaUnsafe L mem0 X ↔ ∃ m r, r ∈ X.objects m ∧ r.fault.isSome := by
  obtain ⟨hCopy, hMasked⟩ := no_linear_copy_faults hX
  constructor
  · rintro (hf | ⟨m, r, hr, hp⟩ | ⟨_, _, _, _, _, _, _, he, hi, hc, hb, _, _⟩ | hf | hf)
    · exact hf
    · exact (hp (mbar_record_published hpre hX hs ht hr)).elim
    · exact (mbar_intent_disjoint hpre hX hs ht he hi hc hb).elim
    · exact (hCopy hf).elim
    · exact (hMasked hf).elim
  · exact Or.inl

/-- The only potentially faulting records are raw-ready arrivals and transaction completions. -/
theorem tmaUnsafe_iff_raw_ready_fault (ht : Frame.Tracked (Machine.code P L) X) :
    TmaUnsafe L mem0 X ↔
      ∃ cta < L.grid, ∃ slot : Fin 2, ∃ r ∈ X.objects ((Protocol.Mbar.rawReady slot).loc L cta),
        r.fault.isSome := by
  rw [tmaUnsafe_iff_record_fault hpre hX hs ht]
  constructor
  · rintro ⟨m, r, hr, hf⟩
    let sound := fun g hg => (hs g hg).machine
    have hn (n : Nat) (ha : r.action = .init n) : False := by
      rw [mbar_init_clean hpre hX hs ht hr ha] at hf
      cases hf
    obtain ⟨cta, hCta, mb, rfl⟩ := mbar_slot_of_noninit hpre hX hs ht hr hn
    cases mb with
    | rawReady slot => exact ⟨cta, hCta, slot, r, hr, hf⟩
    | lastStore =>
      rw [mbar_last_store_clean hpre hX hs ht hr] at hf
      cases hf
    | qTma =>
      rw [mbar_query_load_clean hpre hX hs ht hr] at hf
      cases hf
    | qUtccp =>
      rw [mbar_query_copy_clean hpre hX hs ht hr] at hf
      cases hf
    | rawFree slot =>
      rw [← RawRing.free_loc] at hr
      rw [raw_free_fault_free hpre hX sound ht r hr] at hf
      cases hf
    | validReady slot =>
      rw [index_ready_fault_free hpre hX hCta sound ht r hr] at hf
      cases hf
    | validFree slot =>
      rw [index_free_fault_free hpre hX hCta sound ht r hr] at hf
      cases hf
    | dequantReady slot =>
      have hl : (Protocol.Mbar.dequantReady slot).loc L cta =
          Protocol.GemmRing.Object.dequantReady.loc L cta slot := by fin_cases slot <;> rfl
      rw [hl] at hr
      rw [dequant_ready_fault_free hpre hX sound ht r hr] at hf
      cases hf
    | qkDone slot =>
      have hl : (Protocol.Mbar.qkDone slot).loc L cta =
          Protocol.GemmRing.Object.qkDone.loc L cta slot := by fin_cases slot <;> rfl
      rw [hl] at hr
      rw [qk_done_fault_free hpre hX sound ht r hr] at hf
      cases hf
    | soReady slot =>
      have hl : (Protocol.Mbar.soReady slot).loc L cta =
          Protocol.GemmRing.Object.soReady.loc L cta slot := by fin_cases slot <;> rfl
      rw [hl] at hr
      rw [score_ready_fault_free hpre hX sound ht r hr] at hf
      cases hf
    | svDone slot =>
      rw [sv_done_fault_free hpre hX sound ht r hr] at hf
      cases hf
  · rintro ⟨cta, _, slot, r, hr, hf⟩
    exact ⟨(Protocol.Mbar.rawReady slot).loc L cta, r, hr, hf⟩

/-- No barrier record, publication, overlapping access or linear copy faults. -/
theorem no_tmaUnsafe (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ TmaUnsafe L mem0 X := by
  intro hBad
  obtain ⟨cta, _, slot, r, hr, hf⟩ := (tmaUnsafe_iff_raw_ready_fault hpre hX hs ht).mp hBad
  rw [← RawRing.ready_loc] at hr
  rw [raw_ready_fault_free hpre hX (fun g hg => (hs g hg).machine) ht r hr] at hf
  cases hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

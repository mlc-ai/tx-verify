-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TmaInit
public import Lemmas.Order.GuardSnoc

@[expose] public section

/-! # `TmaUnsafe`, from the thread facts and the rings' facts

Every mbarrier object is one of the ring barriers or an unused barrier of the prologue. The records
of the ring barriers that the rings own are fault-free (`InputFacts`, `TmemFacts`, `ClcFacts`); the
leader-only barriers of the other CTA are only initialized, and an initialization is fault-free
and published (`TmaInit`). No linear copy is issued. An object's bytes lie in the allocated shared
window and outside every byte an access covers (`SharedWindow`). Every mbarrier operand is an
initialization or a ring barrier, which is allocated (`usesMbar_allocated`) and whose
initialization is published to the use (`no_mbarUninit`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A record of a classified ring barrier is fault-free, by its ring's facts. -/
theorem classified_fault_free (hin : InputFacts L X) (htm : TmemFacts L X) (hclc : ClcFacts L X)
    {g j : Nat} {m : Loc} (hc : Classified L X g j m) {r : Record Ref} (hr : r ∈ X.objects m) :
    r.fault = none := by
  obtain ⟨ρ, b, cta, hg, -, hσ, hb, hgrid, hcl, rfl, hlead⟩ := hc
  obtain ⟨ring, sl, f⟩ := b
  simp only [Bar.Valid] at hb
  cases ring <;> cases f <;> simp only [Ring.slots] at hb
  · -- input empty
    have e1 : Bar.loc L cta ⟨.input, sl, false⟩ =
        (InputRing.slot L (cta / 2) ⟨sl, hb⟩).empty ⟨cta % 2, Nat.mod_lt _ (by decide)⟩ := by
      simp only [InputRing.slot, Bar.loc, Loc.mk.injEq, true_and, and_true]
      omega
    exact hin.fault_free (i := (cta / 2, ⟨sl, hb⟩))
      (by rw [e1]; exact MbarRing.RingSlot.empty_mem _ _) r hr
  · -- input full
    have hev := hlead rfl
    have e1 : Bar.loc L cta ⟨.input, sl, true⟩ =
        (InputRing.slot L (cta / 2) ⟨sl, hb⟩).full 0 := by
      simp only [InputRing.slot, Bar.loc, Loc.mk.injEq, true_and, and_true]
      omega
    exact hin.fault_free (i := (cta / 2, ⟨sl, hb⟩))
      (by rw [e1]; exact MbarRing.RingSlot.full_mem _ _) r hr
  · -- accumulator empty
    have hev := hlead rfl
    have e1 : Bar.loc L cta ⟨.acc, sl, false⟩ =
        (TmemRing.slot L (cta / 2) ⟨sl, hb⟩).empty 0 := by
      simp only [TmemRing.slot, Bar.loc, Loc.mk.injEq, true_and, and_true]
      omega
    exact htm.fault_free (i := (cta / 2, ⟨sl, hb⟩))
      (by rw [e1]; exact MbarRing.RingSlot.empty_mem _ _) r hr
  · -- accumulator full
    have e1 : Bar.loc L cta ⟨.acc, sl, true⟩ =
        (TmemRing.slot L (cta / 2) ⟨sl, hb⟩).full ⟨cta % 2, Nat.mod_lt _ (by decide)⟩ := by
      simp only [TmemRing.slot, Bar.loc, Loc.mk.injEq, true_and, and_true]
      omega
    exact htm.fault_free (i := (cta / 2, ⟨sl, hb⟩))
      (by rw [e1]; exact MbarRing.RingSlot.full_mem _ _) r hr
  · -- response barrier, acknowledgement barrier
    have hev := hlead rfl
    have hsl : sl = 0 := by omega
    subst hsl
    have e1 : Bar.loc L cta ⟨.clc, 0, false⟩ = (ClcRing.slot L (cta / 2)).empty 0 := by
      simp only [ClcRing.slot, Bar.loc, Loc.mk.injEq, true_and, and_true]
      omega
    exact hclc.fault_free (i := cta / 2) (by rw [e1]; exact MbarRing.RingSlot.empty_mem _ _) r hr
  · -- response barrier
    have hsl : sl = 0 := by omega
    subst hsl
    have e1 : Bar.loc L cta ⟨.clc, 0, true⟩ =
        (ClcRing.slot L (cta / 2)).full ⟨cta % 2, Nat.mod_lt _ (by decide)⟩ := by
      simp only [ClcRing.slot, Bar.loc, Loc.mk.injEq, true_and, and_true]
      omega
    exact hclc.fault_free (i := cta / 2) (by rw [e1]; exact MbarRing.RingSlot.full_mem _ _) r hr

/-- **Every record of every mbarrier object is fault-free.** -/
theorem record_fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hin : InputFacts L X) (htm : TmemFacts L X) (hclc : ClcFacts L X)
    {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) : r.fault = none := by
  by_cases hn : ∃ n, r.action = .init n
  · obtain ⟨n, ha⟩ := hn
    exact init_record_fault_free hpre hX ht hr ha
  · exact classified_fault_free hin htm hclc
      (noninit_source hpre hX ht hr (fun n h => hn ⟨n, h⟩)) hr

/-- **Synchronization is guarded**: every position of the kernel spins, no write releases and no
mbarrier record faults. -/
theorem syncGuarded (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hin : InputFacts L X) (htm : TmemFacts L X) (hclc : ClcFacts L X) :
    SyncGuarded L kernel X :=
  ⟨fun _ _ _ _ _ _ hw => ht.wait_spins (Frame.lt_of_get hX hw) hw,
    fun e f => ⟨noSynchronizesWith_of ht.no_release
        (fun _ _ _ _ _ h => (no_rmw hX ht h).elim) e f,
      not_fenceSync_of_noFence (fun _ _ _ h => no_threadFence hX ht h) e f⟩,
    fun _ _ _ _ _ hr _ _ _ => record_fault_free hpre hX ht hin htm hclc (List.mem_of_getElem? hr)⟩

/-- The shared bytes of a barrier of a launched CTA, below the shared window's first kilobyte, are
allocated. -/
theorem barrier_allocated (hpre : Pre P L mem0) {m : Loc} (hsp : m.space = .shared)
    (hgrid : m.cta < L.grid) (hlo : L.sharedBase ≤ m.addr) (hhi : m.addr + 8 ≤ L.sharedBase + 1024)
    {l : Loc} (hl : ({ loc := m, size := 8 } : Acc).Covers l) : mem0 l ≠ none := by
  obtain ⟨space, cta, address⟩ := m
  obtain ⟨space', cta', address'⟩ := l
  change space' = space ∧ cta' = cta ∧ address ≤ address' ∧ address' < address + 8 at hl
  obtain ⟨rfl, rfl, h1, h2⟩ := hl
  simp only at hsp hgrid hlo hhi
  subst hsp
  have hb : address' - L.sharedBase < sharedBytes := by unfold sharedBytes; omega
  have hmem := hpre.sharedAllocated cta' hgrid (address' - L.sharedBase) hb
  have heq : (⟨.shared, cta', L.sharedBase + (address' - L.sharedBase)⟩ : Loc) =
      ⟨.shared, cta', address'⟩ := by
    congr 1
    omega
  rw [heq] at hmem
  exact hmem

/-- A barrier of a classified object lies in the first kilobyte of its launched CTA's window. -/
theorem classified_allocated (hpre : Pre P L mem0) {g j : Nat} {m : Loc}
    (hc : Classified L X g j m) {l : Loc} (hl : ({ loc := m, size := 8 } : Acc).Covers l) :
    mem0 l ≠ none := by
  obtain ⟨ρ, b, cta, hg, -, hσ, hb, hgrid, hcl, rfl, hlead⟩ := hc
  have := Bar.off_range hb
  exact barrier_allocated hpre rfl hgrid (by simp only [Bar.loc]; omega)
    (by simp only [Bar.loc]; omega) hl

/-- **An mbarrier operand is an initialization or a classified object.** -/
theorem uses_classified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j : Nat} {m : Loc} (hu : X.UsesMbar (g, j) m) :
    (∃ c, X.MbInit (g, j) m c) ∨ Classified L X g j m := by
  rcases hu with ⟨tx, count, rel, sc, pc, he⟩ | ⟨s, hc, -⟩ | ⟨noinc, ha⟩ |
      ⟨sp, rank, ⟨pc, he⟩, hm⟩ | ⟨pc, p, ok, acq, sc, he⟩ | hv | ⟨address, s, hi, rfl⟩ |
      ⟨s, tg, c, hi, hc, rfl⟩ | hi
  · exact .inr (arrive_classified hpre hX ht he)
  · exact (no_copy hX ht hc).elim
  · exact (no_asyncArrive hX ht ha).elim
  · exact .inr (commit_classified hpre hX ht he hm)
  · exact .inr (wait_classified hpre hX ht he)
  · exact (no_inval hX ht hv).elim
  · exact .inr (tensor_classified hpre hX ht hi)
  · exact .inr (clc_classified hpre hX ht hi hc)
  · exact .inl hi

/-- **Every mbarrier operand is allocated**: a ring barrier, or an initialized barrier, of a
launched CTA's shared window. -/
theorem usesMbar_allocated (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {e : EvId} {m : Loc} (hu : X.UsesMbar e m) {l : Loc}
    (hcov : ({ loc := m, size := 8 } : Acc).Covers l) : mem0 l ≠ none := by
  obtain ⟨g, j⟩ := e
  rcases uses_classified hpre hX ht hu with ⟨c, pci, hi⟩ | hc
  · obtain ⟨h1, h2, -, -, -, hsp, hlo, hhi⟩ := init_site_of hX ht hi
    have hg := Frame.lt_of_get hX hi
    have hgrid : m.cta < L.grid := by
      rw [h2]
      exact cta_lt_grid hpre hg
    exact barrier_allocated hpre hsp hgrid (by omega) (by omega) hcov
  · exact classified_allocated hpre hc hcov

/-- **Every mbarrier operation uses a published initialization**: the ring protocol publishes the
ring barrier's initialization to every classified use (`published_init`). -/
theorem no_mbarUninit (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ¬ MbarUninit L X := by
  rintro ⟨⟨g, j⟩, m, hu, hni, hnp⟩
  rcases uses_classified hpre hX ht hu with ⟨c, hi⟩ | hc
  · exact hni c hi
  · obtain ⟨E, pc, c, hE, hpub⟩ := published_init ht hc
    exact hnp ⟨E, c, ⟨pc, hE⟩, .inl hpub⟩

/-- **No mbarrier object is unsafe.** -/
theorem no_tmaUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hin : InputFacts L X) (htm : TmemFacts L X) (hclc : ClcFacts L X)
    (hwin : SharedWindow L X) : ¬ TmaUnsafe L mem0 X := by
  rintro (⟨m, r, hr, hf⟩ | ⟨m, r, hr, hp⟩ | ⟨e, a, w, i, m, c, l, hint, ⟨pci, hi⟩, hla, hlm, -⟩ |
    hov | hmask)
  · rw [record_fault_free hpre hX ht hin htm hclc hr] at hf
    exact absurd hf (by simp)
  · exact hp (record_published hpre hX ht hr)
  · obtain ⟨-, -, -, -, -, hsp, hlo, hhi⟩ := init_site_of hX ht hi
    have hlsp : l.space = .shared := by
      have : l.space = m.space := hlm.1
      rw [this]
      exact hsp
    have hreg := (hwin e a w l hint hla hlsp).2
    have h2 : m.addr ≤ l.addr ∧ l.addr < m.addr + 8 := ⟨hlm.2.2.1, hlm.2.2.2⟩
    simp only [Region.IsBase, Region.IsResponse, IsInputStage, IsStaging] at hreg
    omega
  · exact not_cpAsyncOverlap_of_none (fun i s hc => (no_copy hX ht hc).elim) hov
  · exact not_maskedRangeUnalloc_of_none (fun i s _ hc => (no_copy hX ht hc).elim) hmask

end PTX.Kernels.Fp16Gemm8192.Proof.Safety

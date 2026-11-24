-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.TmaInit
public import Kernels.FlashAttn4Fwd.Proof.Safety.Memory

@[expose] public section

/-! # `TmaUnsafe`: the mbarrier objects

Every mbarrier object of the kernel is a table barrier of a launched CTA (`record_table`):
initializations are the prologue's, every other operation names a table barrier of its issuer's
pair. Then each part of ERR-OBJECT-LIFETIME:

* **Record faults.** An initialization record is fault-free (`init_fault_free`, from
  `TableInit`). The other records of a Q or KV ring barrier are fault-free by the rings' protocol
  (`RingFaultFree`), those of the handshake barrier by the TMEM-release handshake's
  (`HsFaultFree`), those of the other barriers by theirs (`OtherFaultFree`: the score handoff,
  P-ready, O-full, statistics credit, output staging and free barriers; the spare barriers have
  no other record).
* **Lifetimes.** Every record lies in its barrier's initialization lifetime (`record_published`).
* **Bulk copies.** The kernel issues none (`TmemFacts.no_bulk`).
* **Overlap.** No access touches a barrier's bytes: every shared byte an access touches is in a
  region of the window above the barriers (`SharedPlaced`), and the barriers end at `+328`.
* **Allocation.** A barrier of a launched CTA lies in its shared window (`Pre.sharedAllocated`).
* **Tensor Core collectives.** The thread-level branch `TcUnsafe` is excluded by its own premise
  (the warp-collective `tcgen05` events of the lanes of a warp agree). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The records of the Q and KV ring barriers are fault-free (the rings' `Rings.ring_fault_free`
with `Rings.ringInit`). -/
def RingFaultFree (L : Launch) (X : Execution) : Prop :=
  ∀ {b : FBar}, b.ring → ∀ (cta : Nat) {r : Record Ref}, r ∈ X.objects (b.loc L cta) →
    r.fault = none

/-- The records of the handshake barriers are fault-free (`TmemAlloc.fault_free` with
`InitFirst.deallocInit`). -/
def HsFaultFree (L : Launch) (X : Execution) : Prop :=
  ∀ (cta : Nat) {r : Record Ref}, r ∈ X.objects (FBar.loc L cta .dealloc) → r.fault = none

/-- Every barrier offset leaves room for its eight bytes below the base word. -/
theorem off_le : ∀ b : FBar, b.off ≤ 320 := by decide

/-- The issuer of an mbarrier operation is a launched thread. -/
theorem usesMbar_lt (hX : Consistent L kernel asms mem0 X) {e : EvId} {m : Loc}
    (hu : X.UsesMbar e m) : e.1 < L.threads := by
  obtain ⟨g, k⟩ := e
  rcases hu with ⟨_, _, _, _, _, he⟩ | ⟨_, ⟨_, he⟩, -⟩ | ⟨_, _, he⟩ | ⟨_, _, ⟨_, he⟩, -⟩ |
    ⟨_, _, _, _, _, he⟩ | ⟨_, he⟩ | ⟨_, _, ⟨_, he⟩, -⟩ | ⟨_, _, _, ⟨_, he⟩, -⟩ | ⟨_, _, he⟩ <;>
    exact Frame.lt_of_get hX he

/-- **Every mbarrier object with a record is a table barrier of a launched CTA.** -/
theorem record_table (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hr : RingFacts L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X)
    {m : Loc} {r : Record Ref} (hrm : r ∈ X.objects m) :
    ∃ (b : FBar) (cta : Nat), m = b.loc L cta ∧ cta < L.grid := by
  have hgr := hpre.grid
  have pair : ∀ {e : EvId}, X.UsesMbar e m → ∃ (b : FBar) (cta : Nat), m = b.loc L cta ∧
      cta < L.grid := by
    intro e hu
    obtain ⟨b, c, hm, hc'⟩ := ha.mbar_pair hu
    have := cta_lt (usesMbar_lt hX hu)
    exact ⟨b, c, hm, by omega⟩
  cases record_source hX.tma.2.2.1 hrm with
  | init _ he _ =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨b, hm, -⟩ := hc.init_site hg he
    exact ⟨b, _, hm, cta_lt hg⟩
  | inval _ he _ => exact absurd he htm.no_inval
  | wait _ he _ => exact pair (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩)))))
  | arrive _ he _ => exact pair (.inl ⟨_, _, _, _, _, he⟩)
  | tensor _ he hm _ =>
    obtain ⟨b, c, hring, hm'⟩ := ha.copy_ring he
    have hg := Frame.lt_of_get hX he
    obtain ⟨-, hc', -⟩ := hr.issue hg he hm' hring
    have := cta_lt hg
    refine ⟨b, c, hm.symm.trans hm', ?_⟩
    rw [hc', pairBase]
    omega
  | increment _ he _ => exact absurd he htm.no_arriveOn
  | arriveOn _ he _ _ _ => exact absurd he htm.no_arriveOn
  | bulk _ he _ _ _ => exact absurd he htm.no_bulk
  | commit _ he htg _ => exact pair (.inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, htg⟩))))
  | clc _ he _ _ _ => exact absurd he htm.no_clc

/-- **Every record of every mbarrier object is fault-free.** -/
theorem record_fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hr : RingFacts L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X)
    (hinit : TableInit L X) (hring : RingFaultFree L X) (hhs : HsFaultFree L X)
    (hother : OtherFaultFree L X) {m : Loc} {r : Record Ref} (hrm : r ∈ X.objects m) :
    r.fault = none := by
  obtain ⟨b, cta, rfl, -⟩ := record_table hpre hX hc hr htm ha hrm
  by_cases hn : ∃ n, r.action = .init n
  · exact init_fault_free hinit b cta hrm hn
  · by_cases hd : b = .dealloc
    · subst hd
      exact hhs cta hrm
    cases hb : b.ring
    · exact hother b hb hd cta hrm fun n h => hn ⟨n, h⟩
    · exact hring hb cta hrm

/-- A barrier of a launched CTA lies in its shared window. -/
theorem barrier_allocated (hpre : Pre P L mem0) {b : FBar} {cta : Nat} (hgrid : cta < L.grid)
    {l : Loc} (hl : ({ loc := b.loc L cta, size := 8 } : Acc).Covers l) : mem0 l ≠ none := by
  have hoff := off_le b
  obtain ⟨space, cta', address⟩ := l
  obtain ⟨hs, hc, h1, h2⟩ := hl
  simp only [FBar.loc] at hs hc h1 h2
  subst hs hc
  have hb : address - L.sharedBase < sharedBytes := by unfold sharedBytes; omega
  have hmem := hpre.sharedAllocated _ hgrid (address - L.sharedBase) hb
  rwa [show L.sharedBase + (address - L.sharedBase) = address by omega] at hmem

/-- **The eight bytes of every named mbarrier are allocated**: it is a table barrier of a
launched CTA. -/
theorem mbar_allocated (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ha : AsyncFacts P L X) :
    ∀ e m l, X.UsesMbar e m → Acc.Covers { loc := m, size := 8 } l → mem0 l ≠ none := by
  have hgr := hpre.grid
  intro e m l hu hcov
  obtain ⟨b, c, rfl, hc'⟩ := ha.mbar_pair hu
  have := cta_lt (usesMbar_lt hX hu)
  exact barrier_allocated hpre (by omega) hcov

/-- **No mbarrier object faults or is used unpublished, no initialization is unordered with an
access of its bytes, and the kernel has neither `cp.async` groups nor masked bulk copies.** -/
theorem no_tmaUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hr : RingFacts L X) (htm : TmemFacts L X) (ha : AsyncFacts P L X)
    (hinit : TableInit L X) (hpub : InitsPublished L X) (hring : RingFaultFree L X)
    (hhs : HsFaultFree L X) (hother : OtherFaultFree L X) (hplaced : SharedPlaced L X) :
    ¬ TmaUnsafe L mem0 X := by
  have hgr := hpre.grid
  have hcopy : ∀ i s, X.Copy i s → False := fun i s ⟨pc, he⟩ => htm.no_bulk he
  rintro (⟨m, r, hrm, hf⟩ | ⟨m, r, hrm, hp⟩ |
    ⟨e, a, w, i, m, c, l, hint, ⟨pci, hi⟩, hla, hlm, -⟩ | h | h)
  · rw [record_fault_free hpre hX hc hr htm ha hinit hring hhs hother hrm] at hf
    exact absurd hf (by simp)
  · obtain ⟨b, cta, rfl, -⟩ := record_table hpre hX hc hr htm ha hrm
    exact hp (record_published hpre hX hc hr htm ha hinit hpub b cta hrm)
  · obtain ⟨g, k⟩ := i
    obtain ⟨b, rfl, -⟩ := hc.init_site (Frame.lt_of_get hX hi) hi
    have hoff := off_le b
    obtain ⟨hsp, -, hlo, hhi⟩ := hlm
    simp only [FBar.loc] at hsp hlo hhi
    obtain ⟨-, hreg⟩ := hplaced e a l (.inl ⟨w, hint⟩) hla hsp
    unfold InRegions InBase InStatsArea InStaging InQRing InKvRing at hreg
    rcases hreg with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
  · exact not_cpAsyncOverlap_of_none (fun i s h _ => hcopy i s h) h
  · exact not_maskedRangeUnalloc_of_none (fun i s _ h _ => hcopy i s h) h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety

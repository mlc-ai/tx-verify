-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingRecordSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexRendezvous

@[expose] public section

/-! # Thread memory order for coordinate and mask accesses -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

open PTX PTX.Flow PTX.MbarRing

/-- Reads of one use's coordinates or validity mask. -/
def ConsumerRead (P : Params) (L : Launch) (X : Execution) (g i block : Nat) : Prop :=
  (∃ d : Wg1Tma.D, d.block = block ∧ (∃ k j, d.site = .coord k j) ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) ∨
  (∃ d : Wg0.D, d.block = block ∧ d.site = .maskRead ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))

/-- Writes of one use's coordinates or validity mask. -/
def ProducerWrite (P : Params) (L : Launch) (X : Execution) (g i block : Nat) : Prop :=
  ∃ d : Wg1Index.D, d.block = block ∧
    ((∃ extra hi, d.site = .coord extra hi) ∨ ∃ extra, d.site = .valid extra) ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.index d))

variable {P : Params} {L : Launch}

private theorem read_counts {mem0 : Mem0} {X : Execution} {g i block cta : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hc : ctaOf L g = cta) (hd : ConsumerRead P L X g i block)
    :
    arrivals (free L cta (indexSlot block)) ((X.tr g).take i) = block / 4 ∧
      okPolls (ready L cta (indexSlot block)) ((X.tr g).take i) = block / 4 + 1 := by
  have tr := hs.produces (hX.thr g hg)
  rcases hd with ⟨d, rfl, ⟨k, j, hd⟩, hst⟩ | ⟨d, rfl, hd, hst⟩
  · have h := TmaIndexTrace.composed_coord_counts hpre tr hst hd
    rwa [hc] at h
  · have h := Wg0IndexTrace.composed_mask_read_counts hpre tr hst hd
    rwa [hc] at h

private theorem write_counts {mem0 : Mem0} {X : Execution} {g i block cta : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound) (hc : ctaOf L g = cta) (hd : ProducerWrite P L X g i block)
    :
    arrivals (ready L cta (indexSlot block)) ((X.tr g).take i) = block / 4 ∧
      okPolls (free L cta (indexSlot block)) ((X.tr g).take i) = block / 4 + 1 := by
  obtain ⟨d, rfl, hd, hst⟩ := hd
  have tr := hs.produces (hX.thr g hg)
  have h := IndexRingTrace.composed_write_counts hpre tr hst hd
  change g / L.block = cta at hc
  rwa [hc] at h

/-- A coordinate or mask write precedes reads of its own generation or a later use of its slot. -/
theorem write_before_read_of_generation {mem0 : Mem0} {X : Execution} {cta block earlier i j : Nat}
    {prod : Fin 32 → Nat} {cons : Fin 129 → Nat} {p : Fin 32} {c : Fin 129} {read : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (H : Unit.Ring L kernel Assumptions.all X (ready L cta (indexSlot block))
      (free L cta (indexSlot block)) 32 129 prod cons)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hp : ctaOf L (prod p) = cta)
    (hc : ctaOf L (cons c) = cta) (hSlot : indexSlot earlier = indexSlot block)
    (hUse : earlier / 4 ≤ block / 4) (hw : ProducerWrite P L X (prod p) i earlier)
    (hr : ConsumerRead P L X (cons c) j block) (he : X.get (cons c, j) = some read) :
    baseCausality L X (prod p, i) (cons c, j) := by
  obtain ⟨hgp, hgc, _⟩ := H.cta p c
  have hwrite := (write_counts hpre hX hgp (hs _ hgp) hp hw).1
  rw [hSlot] at hwrite
  have hread := (read_counts hpre hX hgc (hs _ hgc) hc hr).2
  exact (H.full_handoff hX).baseCausality_of_counts ⟨c, rfl⟩ ⟨p, rfl⟩
    (le_of_eq hwrite) (by omega) (PTX.len_of_get he)

/-- A consumer's coordinate or mask read precedes subsequent writes that reuse that slot. -/
theorem read_before_overwrite {mem0 : Mem0} {X : Execution} {cta block later i j : Nat}
    {prod : Fin 32 → Nat} {cons : Fin 129 → Nat} {p : Fin 32} {c : Fin 129} {write : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (H : Unit.Ring L kernel Assumptions.all X (ready L cta (indexSlot block))
      (free L cta (indexSlot block)) 32 129 prod cons)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hp : ctaOf L (prod p) = cta)
    (hc : ctaOf L (cons c) = cta) (hslot : indexSlot block = indexSlot later)
    (huse : block / 4 < later / 4) (hr : ConsumerRead P L X (cons c) i block)
    (hw : ProducerWrite P L X (prod p) j later) (he : X.get (prod p, j) = some write) :
    baseCausality L X (cons c, i) (prod p, j) := by
  obtain ⟨hgp, hgc, _⟩ := H.cta p c
  have hread := (read_counts hpre hX hgc (hs _ hgc) hc hr).1
  have hwrite := (write_counts hpre hX hgp (hs _ hgp) hp hw).2
  rw [← hslot] at hwrite
  exact (H.empty_handoff hX).baseCausality_of_counts ⟨p, rfl⟩ ⟨c, rfl⟩
    (le_of_eq hread) (by omega) (PTX.len_of_get he)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

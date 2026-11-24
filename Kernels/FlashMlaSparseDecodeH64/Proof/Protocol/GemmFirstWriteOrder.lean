-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmCompletion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawRelease
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # Base order of a tile write and its QK consumer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy PTX.Flow PTX.MbarRing

private theorem same_scope {L : Launch} {g h : Nat} (hh : SameCta L g h) (sc : MbarScope) :
    MbarScopeIncludes L sc g h := by
  cases sc
  · exact hh
  · exact ⟨hh.1, hh.2.1, congrArg L.clusterOfCta hh.2.2⟩
  · exact ⟨hh.1, hh.2.1⟩
  · exact ⟨hh.1, hh.2.1⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta issuer i j : Nat}

set_option maxRecDepth 4096 in
/-- The dequantized write precedes the MMA thread's reads for its block through the slot's ready
arrival. The consumer can be the MMA issue itself or its commit. -/
theorem write_before_dequant_consumer {slot : Fin 2} {lane : Fin 128} {d : Wg1Mma.D} {w : Wg2.D}
    {consumer e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hmma : MmaIssuer P L X cta issuer)
    (hc : ctaOf L issuer = cta) (he : X.get (issuer, j) = some consumer)
    (hD : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma d)))
    (hSite : Wg1MmaGemmTrace.completed .dequant d.site = true) (hSlot : d.i % 2 = slot.val)
    (hE : X.get (producer L cta lane, i) = some e)
    (hW : Frame.stateAt (Machine.code P L) X (producer L cta lane) i = some (some (.wg2 w)))
    (hStore : ∃ r k, w.site = .store r k) (hBlock : w.block = d.i) :
    baseCausality L X (producer L cta lane, i) (issuer, j) ∧
      ∃ a e, i ≤ a ∧ X.get (producer L cta lane, a) = some e ∧
        (∃ sc, e.kind = .arrive (full L cta slot) 0 1 true sc) ∧
        baseCausality L X (producer L cta lane, a) (issuer, j) := by
  let g := producer L cta lane
  let m := full L cta slot
  have hg := Frame.lt_of_get hX hE
  have hi := Frame.lt_of_get hX he
  have hCta : ctaOf L g = cta := by
    have := lane.isLt
    simp only [g, RawRing.consumer, ctaOf, hpre.block]
    omega
  have hp := Wg1MmaGemmTrace.composed_count_here hpre hi .dequant
    ((hs issuer hi).produces (hX.thr issuer hi)) hD hSlot
  simp only [hSite, ↓reduceIte] at hp
  change PTX.Flow.okPolls (full L (ctaOf L issuer) slot) ((X.tr issuer).take j) = d.i / 2 + 1 at hp
  rw [hc] at hp
  obtain ⟨k, kt, parity, acq, ws, hkj, hk, hkCount⟩ := Poll.exists_nth hp.ge
  obtain ⟨rfl, _⟩ := RingSourceSites.actual_wait_acquire hX hk rfl
  let R := dequantRing (slot := slot) hpre hX hs hmma
  have hnth : Poll.nth X m issuer (d.i / 2) = k := by rw [← hkCount, Poll.nth_eq hk]
  have hPres : X.RefPresent (.thread (R.wF 0 (d.i / 2))) := by
    change X.RefPresent (.thread (issuer, Poll.nth X m issuer (d.i / 2)))
    rw [hnth]
    exact ⟨_, hk⟩
  obtain ⟨hItem, hWitness⟩ := R.observes_full hX.depAcyclic hPres lane
  let F := dequant_obj (cta := cta) (slot := slot) hpre hX hs
  obtain ⟨_, ⟨arrTag, ascope, hArrive⟩, hOrdinal⟩ := F.S_rec hItem
  let a := (Unit.it X m (producer L cta) lane (d.i / 2)).2
  change PTX.Flow.arrivals m ((X.tr g).take a) = d.i / 2 at hOrdinal
  obtain ⟨hCount, _⟩ := Wg2GemmTrace.composed_write_counts hpre
    ((hs g hg).produces (hX.thr g hg)) hW hStore
  rw [hCta, hBlock, hSlot] at hCount
  change PTX.Flow.arrivals m ((X.tr g).take i) = d.i / 2 at hCount
  have hm : Object.dequantReady.loc L cta slot = m := rfl
  have hLe : i ≤ a := arrival_index_ge hArrive
    (by simpa [arrivesOn, sourceArrive] using hm)
    hOrdinal hCount.le
  change Witness L X (.thread (g, a)) (issuer, Poll.nth X m issuer (d.i / 2)) at hWitness
  rw [hnth] at hWitness
  have hSync (n : Nat) (hn : n ≤ a) : MSync L X (g, n) (issuer, j) := by
    exact ⟨(g, a), (issuer, k), m, ascope, ws, ⟨0, 1, arrTag, hArrive⟩,
      (hWitness.waitObserves hk).2,
      ⟨same_scope ⟨hg, hi, hCta.trans hc.symm⟩ ascope,
        same_scope ⟨hi, hg, hc.trans hCta.symm⟩ ws⟩,
      rfl, hkj, PTX.len_of_get he, rfl, hn⟩
  exact ⟨.single (.inr (.inr (.inl (hSync i hLe)))),
    a, _, hLe, hArrive, ⟨ascope, rfl⟩,
    .single (.inr (.inr (.inl (hSync a le_rfl))))⟩

/-- A dequant store's own proxy fence orders its shared bytes before the consuming MMA. -/
theorem dequant_proxy_before_consumer {slot : Fin 2} {lane : Fin 128} {d : Wg1Mma.D} {w : Wg2.D}
    {consumer e : Event} {byte : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hmma : MmaIssuer P L X cta issuer)
    (hc : ctaOf L issuer = cta) (he : X.get (issuer, j) = some consumer)
    (hD : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma d)))
    (hSite : Wg1MmaGemmTrace.completed .dequant d.site = true) (hSlot : d.i % 2 = slot.val)
    (hE : X.get (producer L cta lane, i) = some e)
    (hW : Frame.stateAt (Machine.code P L) X (producer L cta lane) i = some (some (.wg2 w)))
    (hStore : ∃ r k, w.site = .store r k) (hBlock : w.block = d.i)
    (hkind : ∃ fp bs, e.kind = .wr fp bs) (hspace : byte.space = .shared) (hbyte : byte.cta = cta) :
    ProxyBefore L X (producer L cta lane, i) (issuer, j) byte := by
  let g := producer L cta lane
  obtain ⟨_, a, arr, ha, harr, ⟨scope, hkindArr⟩, hAfter⟩ :=
    write_before_dequant_consumer hpre hX hs hmma hc he hD hSite hSlot hE hW hStore hBlock
  have hg := Frame.lt_of_get hX harr
  have hi := Frame.lt_of_get hX he
  have hFollow := MachineTracking.tracked_nonsoftmax_wg hpre hX
    (fun _ hg => Machine.code_sound hpre hg) (show wgOf L g ≠ 0 by
      rw [producer_wg2 hpre cta lane]; decide) a
  obtain ⟨⟨hcta, ad, _, hReady, hAd⟩, _, _, _, _⟩ :=
    arrival_at_followed hpre hX (hs g hg) hFollow harr hkindArr
  obtain ⟨f, hfa, ⟨tag, hf⟩⟩ :=
    Wg2RawRelease.fence_before_ready hX (hs g hg) harr hAd hReady
  have hiNeArr : i ≠ a := by
    rintro rfl
    obtain ⟨fp, bs, hk⟩ := hkind
    have := congrArg Event.kind (Option.some.inj (hE.symm.trans harr))
    rw [hk, hkindArr] at this
    cases this
  have hiNeFence : i ≠ f := by
    rintro rfl
    obtain ⟨fp, bs, hk⟩ := hkind
    have := congrArg Event.kind (Option.some.inj (hE.symm.trans hf))
    rw [hk] at this
    cases this
  have hbefore : baseCausality L X (g, i) (g, f) :=
    .single (.inl (po_of_not_access rfl (by omega) (PTX.len_of_get hf) (by rw [hf]; rfl)))
  have hfa' : baseCausality L X (g, f) (g, a) :=
    .single (.inl (po_of_source_not_access rfl (by omega) (PTX.len_of_get harr) (by rw [hf]; rfl)))
  exact ⟨(g, f), _, none, ⟨tag, hf⟩, hg, ⟨hspace, hbyte.trans hcta.symm⟩,
    ⟨hg, hi, congrArg L.clusterOfCta (hcta.trans hc.symm)⟩, hbefore, hfa'.trans hAfter⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

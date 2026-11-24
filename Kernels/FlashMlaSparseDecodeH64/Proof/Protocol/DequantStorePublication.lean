-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2StoreHistory
import Lemmas.Order.OrderBaseCausality
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs

@[expose] public section

/-! # The writes behind an observed dequantized tile -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantStorePublication

open PTX PTX.Proof PTX.Flow PTX.MbarRing GemmRing Wg2 Wg2.Numeric

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {cta issuer i tag parity use : Nat} {slot : Fin 2} {sc : MbarScope}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hmma : MmaIssuer P L X cta issuer)
    (he : X.get (issuer, i) = some ⟨tag, .wait (full L cta slot) parity true true sc⟩)
    (hn : PTX.Flow.okPolls (full L cta slot) ((X.tr issuer).take i) = use)
include hpre hX hs hmma he hn

set_option maxRecDepth 4096 in
/-- An actual successful acquire observes the selected producer's ready event for the
corresponding use of this slot. -/
theorem ready_of_wait (lane : Fin 128) :
    let g := producer L cta lane
    let j := (Unit.it X (full L cta slot) (producer L cta) lane use).2
    ∃ (d : Wg2.D) (readyTag : Nat),
      X.get (g, j) = some ⟨readyTag, .arrive (full L cta slot) 0 1 true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)) ∧
      d.site = .ready ∧ d.block = 2 * use + slot.val ∧
      Witness L X (.thread (g, j)) (issuer, i) := by
  let R := dequantRing (slot := slot) hpre hX (fun g hg => (hs g hg).machine) hmma
  have hi : Poll.nth X (full L cta slot) issuer use = i := by
    rw [← hn]
    exact Poll.nth_eq he
  have hPresent : X.RefPresent (.thread (R.wF 0 use)) := by
    change X.RefPresent (.thread (issuer, Poll.nth X (full L cta slot) issuer use))
    rw [hi]
    exact ⟨_, he⟩
  obtain ⟨hmem, hObs⟩ := R.observes_full hX.depAcyclic hPresent lane
  let g := producer L cta lane
  let j := (Unit.it X (full L cta slot) (producer L cta) lane use).2
  change (lane, use) ∈ Unit.S X (full L cta slot) (producer L cta) at hmem
  change Witness L X (.thread (g, j)) (issuer, Poll.nth X (full L cta slot) issuer use) at hObs
  rw [hi] at hObs
  obtain ⟨_, ⟨readyTag, scope, hr⟩, hCount⟩ :=
    (dequant_obj hpre hX (fun g hg => (hs g hg).machine)).S_rec hmem
  have hg := Frame.lt_of_get hX hr
  have hFollow := MachineTracking.tracked_nonsoftmax_wg hpre hX hs
    (show wgOf L g ≠ 0 by rw [producer_wg2 hpre cta lane]; decide) j
  obtain ⟨⟨hcta, d, hslot, hsite, hstate⟩, _, _, _, hscope⟩ :=
    arrival_at_followed hpre hX (hs g hg).machine hFollow hr rfl
  obtain ⟨hArr, _⟩ := Wg2GemmTrace.composed_publication_counts hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hstate hsite
  rw [hcta, hslot] at hArr
  change PTX.Flow.arrivals (full L cta slot) ((X.tr g).take j) = d.block / 2 at hArr
  change PTX.Flow.arrivals (full L cta slot) ((X.tr g).take j) = use at hCount
  have hb : d.block = 2 * use + slot.val := by omega
  rw [hscope] at hr
  exact ⟨d, readyTag, hr, hstate, hsite, hb, hObs⟩

/-- Every requested row and step was stored before the actual ready event observed by the
acquire. The result identifies the fired store, its payload, and its shared footprint. -/
theorem store_of_wait (lane : Fin 128) (r : Fin 4) (s : Fin 8) :
    let g := producer L cta lane
    let j := (Unit.it X (full L cta slot) (producer L cta) lane use).2
    ∃ (d q : Wg2.D) (readyTag k : Nat) (e : Event) (u : TState) (a : Acc),
      X.get (g, j) = some ⟨readyTag, .arrive (full L cta slot) 0 1 true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)) ∧
      d.site = .ready ∧
      k + (81 - Wg2StoreHistory.storeOrdinal r s) = j ∧ q.block = 2 * use + slot.val ∧
      q.site = .store r s ∧ Frame.stateAt (Machine.code P L) X g k = some (some (.wg2 q)) ∧
      X.get (g, k) = some e ∧ (Machine.machine P L g).Fired (some (.wg2 q)) e (some u) ∧
      e.kind = .wr a (dequantChunk q.raw (byteAt q.sc (scaleIdx L g s.val))).toBytes ∧
      a.loc = ⟨.shared, cta, L.sharedBase + tileBase slot.val + tileOff L g r.val s.val⟩ ∧
      a.size = 16 ∧ po X (g, k) (g, j) ∧ Witness L X (.thread (g, j)) (issuer, i) := by
  obtain ⟨d, rt, hr, hd, hsite, hb, hObs⟩ := ready_of_wait hpre hX hs hmma he hn lane
  let g := producer L cta lane
  let j := (Unit.it X (full L cta slot) (producer L cta) lane use).2
  have hg := Frame.lt_of_get hX hr
  obtain ⟨k, q, ev, u, a, hDist, hk, hBlock, hqs, hq, hGet, hFire, hKind, hLoc, hSize⟩ :=
    Wg2StoreHistory.store_before_ready hpre hX (hs g hg).machine hr hd hsite r s
  have hCta : ctaOf L g = cta := by
    have hLane := lane.isLt
    simp only [g, RawRing.consumer, ctaOf, hpre.block]
    omega
  have hSlot : d.block % 2 = slot.val := by
    have := slot.isLt
    omega
  rw [hCta, hSlot] at hLoc
  have hPo : po X (g, k) (g, j) :=
    po_of_not_access rfl hk (PTX.len_of_get hr) (by rw [hr]; rfl)
  exact ⟨d, q, rt, k, ev, u, a, hr, hd, hsite, hDist, hBlock.trans hb, hqs, hq, hGet,
    hFire, hKind, hLoc, hSize, hPo, hObs⟩

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantStorePublication

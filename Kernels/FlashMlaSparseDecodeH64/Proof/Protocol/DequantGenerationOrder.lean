-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmFirstWriteOrder
import Lemmas.Order.Order

@[expose] public section

/-! # Writes of successive uses of one dequantization slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable {g i j : Nat} {d d' : Wg2.D} {a a' : Acc} {bs bs' : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hj : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d')))
    (hSite : ∃ r s, d.site = .store r s) (hSite' : ∃ r s, d'.site = .store r s)
    (hw : X.Writes (g, i) a bs) (hw' : X.Writes (g, j) a' bs') (ha : a.Covers l) (ha' : a'.Covers l)
include hpre hX hs hi hj hSite hSite' hw hw' ha ha'

/-- Ready-arrival counts order two overlapping dequantization writes of the same lane. -/
theorem dequant_generation_base (hslot : d.block % 2 = d'.block % 2) (hblock : d.block < d'.block) :
    baseCausality L X (g, i) (g, j) := by
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  have htrace := hs.produces (hX.thr g hg)
  have hCount := (Wg2GemmTrace.composed_write_counts hpre htrace hi hSite).1
  have hCount' := (Wg2GemmTrace.composed_write_counts hpre htrace hj hSite').1
  let m : Loc := ⟨.shared, ctaOf L g, L.sharedBase + Wg2.dequantReadyOff (d.block % 2)⟩
  change arrivals m ((X.tr g).take i) = d.block / 2 at hCount
  rw [← hslot] at hCount'
  change arrivals m ((X.tr g).take j) = d'.block / 2 at hCount'
  have hij : i < j := by
    by_contra h
    have hmono := countP_take_mono (arrivesOn m) (X.tr g) (Nat.le_of_not_lt h)
    change arrivals m ((X.tr g).take j) ≤ arrivals m ((X.tr g).take i) at hmono
    omega
  exact .single (.inl (po_of_overlap hw.access hw'.access rfl hij ⟨l, ha, ha'⟩))

/-- The base order of two overlapping generations gives byte causality for their writes. -/
theorem dequant_generation_before (hslot : d.block % 2 = d'.block % 2) (hblock : d.block < d'.block)
    :
    ByteCausality L X l (.thread (g, i)) (.thread (g, j)) := by
  exact .direct (modelCausality.of_base L
    (dequant_generation_base hpre hX hs hi hj hSite hSite' hw hw' ha ha' hslot hblock))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

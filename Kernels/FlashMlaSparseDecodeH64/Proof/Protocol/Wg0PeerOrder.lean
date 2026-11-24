-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead
import Lemmas.Flow.Final
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The ordering of the two softmax warps' shared score exchange -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerOrder

open PTX PTX.Flow Wg0 Wg0PeerTrace

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

/-- The named exchange barrier joins warps zero and two or warps one and three. -/
def pairWarps (p : Fin 2) : Finset Nat := {p.val, p.val + 2}

theorem pairShape {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (p : Fin 2) :
    NamedBar.Shape L (some 64) (pairWarps p) (10 + p.val) := by
  have hp := p.isLt
  have hcard : (pairWarps p).card = 2 := by fin_cases p <;> decide
  refine ⟨by omega, ?_, ?_, by omega⟩
  · rw [hpre.block, hcard]
    rfl
  · intro w hw
    simp only [pairWarps, Finset.mem_insert, Finset.mem_singleton] at hw
    rw [hpre.block]
    omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Actual arrivals on a pair barrier use its two warps and the 64-thread count. -/
theorem pairSources (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (p : Fin 2) :
    NamedBar.Sources L X (some 64) (pairWarps p) (10 + p.val) := by
  rintro ⟨g, k⟩ tag count ⟨mode, he⟩ _
  obtain ⟨hw, hp, hc, _⟩ := MachineTracking.actual_pair_bar (p := p) hpre hX hs he
  refine ⟨?_, hc⟩
  have hwarp : warpOf L g ∈ pairWarps p := by
    simp only [pairWarps, Finset.mem_insert, Finset.mem_singleton]
    omega
  simpa only [warpOf, tidOf_eq hpre, hpre.block] using hwarp

/-- Two actual pair arrivals of the same block order the accesses before and after them. -/
theorem same_block_order {writer reader wb rb before after tag tag' : Nat} {dw dr : Wg0.D}
    {p : Fin 2} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hcta : SameCta L writer reader)
    (hw : X.IsBarrier (writer, wb) (10 + p.val) (some 64) tag)
    (hr : X.IsBarrier (reader, rb) (10 + p.val) (some 64) tag')
    (hdw : Frame.stateAt (Machine.code P L) X writer wb = some (some (.wg0 dw)))
    (hdr : Frame.stateAt (Machine.code P L) X reader rb = some (some (.wg0 dr)))
    (hblock : dw.block = dr.block) (hb : before < wb) (ha : rb < after)
    (hlen : after < (X.tr reader).length) :
    baseCausality L X (writer, before) (reader, after) := by
  obtain ⟨_, hfw⟩ := (Frame.trace hs hX hcta.1).fired_at hw hdw
  obtain ⟨_, hfr⟩ := (Frame.trace hs hX hcta.2.1).fired_at hr hdr
  obtain ⟨_, hW, hsw, _, hpw, _, _⟩ := pair_fired (p := p) hpre hfw rfl
  obtain ⟨_, hR, hsr, _, hpr, _, _⟩ := pair_fired (p := p) hpre hfr rfl
  cases hW
  cases hR
  have how := pairOrdinal hpre hX (hs writer hcta.1).machine hw hdw hsw
  have hor := pairOrdinal hpre hX (hs reader hcta.2.1).machine hr hdr hsr
  rw [hpw] at how
  rw [hpr] at hor
  exact (pairSources hpre hX hs p).same_ordinal_baseCausality hX (pairShape hpre p)
    hcta hw hr (by omega) (how.trans (hblock.trans hor.symm)) hb ha hlen

/-- The actual read and write footprints line up in the same CTA and exchange group, with
the consumer selecting one eight-byte element of the peer's 16-byte vector. -/
theorem matching_accesses {writer reader i j : Nat} {dw dr : Wg0.D} {ew er : Event} {group : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hew : X.get (writer, i) = some ew)
    (her : X.get (reader, j) = some er)
    (hdw : Frame.stateAt (Machine.code P L) X writer i = some (some (.wg0 dw)))
    (hdr : Frame.stateAt (Machine.code P L) X reader j = some (some (.wg0 dr)))
    (hw : dw.site = .exchStore group) (hr : dr.site = .peerRead group) (hnw : ew.kind ≠ .exit)
    (hnr : er.kind ≠ .exit) (huw : ∀ f, ew.kind ≠ .ub f) (hur : ∀ f, er.kind ≠ .ub f)
    (hcta : ctaOf L writer = ctaOf L reader) (hlane : laneOf L writer = laneOf L reader)
    (hwarp : warpOf L writer ^^^ 2 = warpOf L reader) :
    ∃ a bytes ac values,
      X.Writes (writer, i) a bytes ∧ X.Reads (reader, j) ac values ∧
      bytes = (exchangeValue dw group.val).toBytes ∧
      ac.loc = a.loc.at (8 * dr.sub) ∧ a.size = 16 ∧ ac.size = 8 ∧ dr.sub < 2 := by
  obtain ⟨tw, iw, ow, htw, hiw, hcw, hfw⟩ := Frame.fired_site hs hX hew hdw
  obtain ⟨tr, ir, or, htr, hir, hcr, hfr⟩ := Frame.fired_site hs hX her hdr
  cases ow with
  | none =>
    rcases fires_none_ends hfw with ⟨f, h⟩ | h
    · exact (huw f h).elim
    · exact (hnw h).elim
  | some uw =>
    cases or with
    | none =>
      rcases fires_none_ends hfr with ⟨f, h⟩ | h
      · exact (hur f h).elim
      · exact (hnr h).elim
    | some ur =>
      obtain ⟨a, hwrite, haw, hsizew, _⟩ :=
        fires_exchangeStore hpre group hw htw hiw hcw hfw
      obtain ⟨ac, values, hread, har, hsizer, _⟩ :=
        fires_peerRead_at hpre hr hir htr hcr hfr
      have hi : Inv P L reader dr := hir
      have hsub : dr.sub < 2 := by simpa only [hr, Site.elems] using hi.subLt
      have hrSize : ac.size = 8 := by rw [hsizer, hr]; rfl
      have hloc : ac.loc = a.loc.at (8 * dr.sub) := by
        simp only [siteLoc, hw, hr, Option.some.injEq] at haw har
        rw [← haw, ← har]
        simp only [shLoc, Loc.at, hcta, hlane, hwarp, Nat.add_assoc]
      refine ⟨a, _, ac, values, ?_, ?_, rfl, hloc, hsizew, hrSize, hsub⟩
      · obtain ⟨tag, kind⟩ := ew
        change kind = _ at hwrite
        exact ⟨tag, by rwa [← hwrite]⟩
      · obtain ⟨tag, kind⟩ := er
        change kind = _ at hread
        exact ⟨tag, by rwa [← hread]⟩

/-- The actual consumer has passed the pair arrival of the block it is reading. -/
theorem pair_before_read {g i : Nat} {d : Wg0.D} {e : Event} {group : Fin 8} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hr : d.site = .peerRead group) :
    ∃ j < i, ∃ tag b,
      X.IsBarrier (g, j) (10 + warpOf L g % 2) (some 64) tag ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 b)) ∧
      b.site = .pairBar ∧ b.block = d.block := by
  let p : Fin 2 := ⟨warpOf L g % 2, Nat.mod_lt _ (by decide)⟩
  have hcount := peerOrdinal hpre hX hs he hd hr
  obtain ⟨j, ev, hji, hev, hform, hord⟩ := exists_nthEv hcount.ge
  obtain ⟨tag, cnt, mode, hk⟩ := NamedBar.isBarId_form hform
  obtain ⟨q, hState⟩ := FollowedPrefix.state_at hd hji.le
  obtain ⟨_, hf⟩ := (hs.produces (hX.thr g (Frame.lt_of_get hX hev))).fired_at hev hState
  obtain ⟨b, rfl, hsite, _, _, hcnt, hmode⟩ :=
    pair_fired (p := p) hpre hf (congrArg Event.kind hk)
  have hb := hState
  have hOrdinal := pairOrdinal hpre hX hs hev hb hsite
  refine ⟨j, hji, tag, b, ?_, hb, hsite, hOrdinal.symm.trans hord⟩
  rw [hk, hcnt, hmode] at hev
  exact hev

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerOrder

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreEventHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadbackSource
import Lemmas.Step.CtaBarNamed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingClosing
import Lemmas.Tcgen05.TcMmaRead
import Lemmas.Tmem.TmemPairHistory

@[expose] public section

/-! # Score loads finish before their CTA releases Tensor Memory -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime

open PTX PTX.Flow Tmem.Pair MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

private abbrev warps : Finset Nat := Finset.range 12

private theorem warp_bound (hpre : Pre P L mem0) :
    ∀ w ∈ warps, w < L.block / 32 := by
  intro w hw
  rw [hpre.block]
  exact Finset.mem_range.mp hw

private theorem close_protocol {c : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hc : c < L.grid) :
    PTX.NamedBar.Protocol none warps 12 (X.barriers c) := by
  apply PTX.NamedBar.protocol_of_src hX ?_ hc (by rw [hpre.block]; decide)
  intro e tag cnt he _
  obtain ⟨hn, _⟩ := actual_gate_fields hpre hX hs he
  refine ⟨Finset.mem_range.mpr ?_, hn⟩
  rw [hpre.block]
  have := Nat.mod_lt e.1 (by decide : 0 < 384)
  omega

section
variable {g h w j release bv : Nat}

/-- A softmax event before closing is ordered before an event behind the released CTA gate. -/
private theorem elapsed_closing_order_of_lane (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hCta : SameCta L g h)
    (hBefore : ∀ {i tag}, X.get (g, i) = some ⟨tag, .bar 12 none .sync⟩ → w < i)
    (hbar : X.get (h, j) = some ⟨bv, .bar 12 none .sync⟩) (hpassed : j + 1 < (X.tr h).length)
    (hjr : j < release) (hrel : release < (X.tr h).length)
    (hexitClose : (∃ n tag, X.get (g, n) = some ⟨tag, .exit⟩) →
      ∃ n tag, X.get (g, n) = some ⟨tag, .bar 12 none .sync⟩) :
    baseCausality L X (g, w) (h, release) := by
  let c := h / L.block
  have hpos : 0 < L.block := by rw [hpre.block]; decide
  have hgrid : c < L.grid := (Nat.div_lt_iff_lt_mul hpos).mpr hCta.2.1
  have hprot := close_protocol (c := c) hpre hX hs hgrid
  have hn : 0 < (12 : Nat) := by decide
  have hcount : CtaBarrier.target L.block none = .ok 12 := by rw [hpre.block]; rfl
  have hcard : warps.card = 12 := by simp
  have hid : 12 < 16 := by decide
  have hwarp (q : Nat) : (q % L.block) / 32 ∈ warps := by
    rw [hpre.block]
    have := Nat.mod_lt q (by decide : 0 < 384)
    exact Finset.mem_range.mpr (by omega)
  by_cases hexit : ∃ n tag, X.get (g, n) = some ⟨tag, .exit⟩
  · obtain ⟨n, tag, hgbar⟩ := hexitClose hexit
    have hbefore := hBefore hgbar
    have hpref : PTX.NamedBar.PrefixFor L X none warps 12 (h, j) := by
      intro index warp count lanes hr _
      refine ⟨?_, hprot _ (List.mem_of_getElem? hr) rfl⟩
      intro r hm
      exact hprot r (List.mem_of_mem_take hm)
    have hord := (actual_gate_ordinal hpre hX hs hgbar).trans
      (actual_gate_ordinal hpre hX hs hbar).symm
    exact PTX.NamedBar.reached_same_ordinal_baseCausality hX hn hcount hid hCta hgbar hbar hpassed
      (hwarp g) hpref hord (fun _ _ r hm => hprot r (List.mem_of_mem_take hm))
      hcard (warp_bound hpre) hbefore hjr hrel
  · obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hbar hpassed
    obtain ⟨count, tag, hk⟩ := hkey.2.1
    have hk' := Kind.bar.inj
      (congrArg Event.kind (Option.some.inj (hk.symm.trans hbar)))
    have hm : key % 16 = 12 := hk'.1
    have hkEq : 12 + 16 * (key / 16) = key := by omega
    have hdone' : CtaBarrier.Released L.block (X.barriers c) 12 (key / 16) := by
      change CtaBarrier.Released L.block (X.barriers c) (key % 16) (key / 16) at hdone
      rwa [hm] at hdone
    have hgl : g % L.block < L.block := Nat.mod_lt _ hpos
    have hge : c * L.block + g % L.block = g := by
      change h / L.block * L.block + g % L.block = g
      rw [← hCta.2.2, Nat.mul_comm]
      exact Nat.div_add_mod g L.block
    obtain ⟨e, etag, hthread, he, _, ha⟩ := PTX.NamedBar.released_member_key hX hn
      hcount hgrid hid hdone' (fun _ _ r hm => hprot r (List.mem_of_mem_take hm))
      hcard (warp_bound hpre) hgl (hwarp g)
      (by intro n tag hh; rw [hge] at hh; exact hexit ⟨n, tag, hh⟩)
    rw [hkEq] at ha
    obtain ⟨ge, n⟩ := e
    dsimp only at hthread
    rw [hge] at hthread
    subst ge
    have hbefore := hBefore he
    exact .single (.inr (.inl ⟨hCta, key, n, j, ha.arrival, hkey, hbefore, hjr, hrel⟩))

/-- A softmax event before closing is ordered before an event behind the released CTA gate. -/
theorem elapsed_closing_order {sd : Wg0.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hCta : SameCta L g h) (hwait : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 sd)))
    (hNotClosing : sd.site ≠ .everyone) (hNotExit : sd.site ≠ .exit) (hw : w ≤ (X.tr g).length)
    (hbar : X.get (h, j) = some ⟨bv, .bar 12 none .sync⟩) (hpassed : j + 1 < (X.tr h).length)
    (hjr : j < release) (hrel : release < (X.tr h).length)
    (hexitClose : (∃ n tag, X.get (g, n) = some ⟨tag, .exit⟩) →
      ∃ n tag, X.get (g, n) = some ⟨tag, .bar 12 none .sync⟩) :
    baseCausality L X (g, w) (h, release) :=
  elapsed_closing_order_of_lane hpre hX hs hCta
    (fun he => ScoreClosingGate.wg0_before_closing hpre hX hs ht he hwait hNotClosing hNotExit hw)
    hbar hpassed hjr hrel hexitClose
end

/-- A passed closing gate supplies the actual closing arrival of a WG0 lane in its CTA. -/
theorem closing_member {g h j tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hCta : SameCta L g h)
    (hbar : X.get (h, j) = some ⟨tag, .bar 12 none .sync⟩)
    (hpassed : j + 1 < (X.tr h).length)
    (hexitClose : (∃ n tag, X.get (g, n) = some ⟨tag, .exit⟩) →
      ∃ n tag, X.get (g, n) = some ⟨tag, .bar 12 none .sync⟩) :
    ∃ i tag, X.get (g, i) = some ⟨tag, .bar 12 none .sync⟩ := by
  by_cases hexit : ∃ n tag, X.get (g, n) = some ⟨tag, .exit⟩
  · exact hexitClose hexit
  let c := h / L.block
  have hpos : 0 < L.block := by rw [hpre.block]; decide
  have hgrid : c < L.grid := (Nat.div_lt_iff_lt_mul hpos).mpr hCta.2.1
  have hprot := close_protocol (c := c) hpre hX hs hgrid
  have hcount : CtaBarrier.target L.block none = .ok 12 := by rw [hpre.block]; rfl
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hbar hpassed
  obtain ⟨count, tag', hk⟩ := hkey.2.1
  have hm : key % 16 = 12 := (Kind.bar.inj
    (congrArg Event.kind (Option.some.inj (hk.symm.trans hbar)))).1
  have hdone' : CtaBarrier.Released L.block (X.barriers c) 12 (key / 16) := by
    change CtaBarrier.Released L.block (X.barriers c) (key % 16) (key / 16) at hdone
    rwa [hm] at hdone
  have hge : c * L.block + g % L.block = g := by
    change h / L.block * L.block + g % L.block = g
    rw [← hCta.2.2, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  have hwarp : g % L.block / 32 ∈ warps := by
    rw [hpre.block]
    have := Nat.mod_lt g (by decide : 0 < 384)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨e, etag, he, hget, _, _⟩ := PTX.NamedBar.released_member_key hX
    (by decide : 0 < 12) hcount hgrid (by decide : 12 < 16) hdone'
    (fun _ _ r hm => hprot r (List.mem_of_mem_take hm)) (by simp : warps.card = 12)
    (warp_bound hpre) (Nat.mod_lt _ hpos) hwarp
    (by intro n tag hh; rw [hge] at hh; exact hexit ⟨n, tag, hh⟩)
  rw [hge] at he
  rcases e with ⟨a, k⟩
  dsimp only at he
  subst a
  exact ⟨k, etag, hget⟩

/-- The kernel releases allocations through its actual single-CTA deallocation request. -/
theorem release_source {c : Nat} {r : Requests} {e : EvId}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hr : r ∈ X.tmemHistory c)
    (he : ReleaseOf L X r e) :
    e.1 / L.block = r.own.cta ∧
      ∃ tag group base n, X.get e = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩ := by
  rcases he with he | ⟨pair, hm, _⟩
  · obtain ⟨n, base, tag, _, ⟨group, hget⟩, hc⟩ := he
    refine ⟨?_, tag, group, base, n, hget⟩
    rcases hc with ⟨lane, hl, _, _⟩ | hc
    · rw [hl]
      exact (WarpRequest.event_props ((hX.tmemPair.1 c).1 _ hr).2.2 lane).1
    · exact hc.1
  · have hp := (hX.tmemPair.2.1 pair hm).1
    have hone := (ScoreReleaseTrace.resource_source hX (hp.2.1.2.2.1 0)).1
    cases hone

private theorem sourceLive_of_wait_order
    {g ld wait tag : Nat} {reg : Nat} {cell : TcMma.Cell} {source : EvId}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hload : TcMma.LoadCell L X (g, ld) reg cell) (horder : ld < wait)
    (hwait : X.get (g, wait) = some ⟨tag, .tc .waitLd⟩)
    (hOrder : ∀ {h k rtag base n} {group}, SameCta L g h →
      X.get (h, k) = some ⟨rtag, .tc (.resource group none (.dealloc base n))⟩ →
      baseCausality L X (g, wait) (h, k)) :
    TcMma.SourceLive L X source (g, ld) cell := by
  intro c r hr hcover release hre
  obtain ⟨hcta, rtag, group, base, n, hget⟩ := release_source hX hr hre
  obtain ⟨_, _, _, howner, _, _, _⟩ := hcover
  obtain ⟨h, k⟩ := release
  have hscope : SameCta L g h :=
    ⟨Frame.lt_of_get hX hwait, Frame.lt_of_get hX hget, hload.owner.symm.trans
      (howner.trans hcta.symm)⟩
  have hbarrier := hOrder hscope hget
  obtain ⟨_, _, _, ⟨ldtag, hld⟩, _, _⟩ := hload
  refine .inl ⟨fun _ => ⟨(g, wait), ⟨tag, hwait⟩, rfl, horder, .inl hbarrier⟩, ?_, ?_⟩
  · rintro ⟨_, _, _, _, hother⟩
    rw [hld] at hother
    cases hother
  · rintro (⟨_, _, _, _, _, hother⟩ | ⟨_, _, hother⟩ | ⟨_, _, hother⟩) <;>
      rw [hld] at hother <;> cases hother

section
variable {g ld wait tag : Nat} {d : Wg0.D} {reg : Nat} {cell : TcMma.Cell} {source : EvId}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hload : TcMma.LoadCell L X (g, ld) reg cell)
    (hstate : Frame.stateAt (Machine.code P L) X g wait = some (some (.wg0 d)))
include hpre hX hs hload hstate

/-- All three load waits precede the actual release of the covering allocation. -/
theorem sourceLive_of_actual_load_wait (hsite : SoftmaxLoadWaitSite d.site = true)
    (horder : ld < wait) (hwait : X.get (g, wait) = some ⟨tag, .tc .waitLd⟩) :
    TcMma.SourceLive L X source (g, ld) cell := by
  apply sourceLive_of_wait_order hX hload horder hwait
  intro h k rtag base n group hscope hget
  obtain ⟨j, bt, hj, hGate⟩ := actual_gate_before_dealloc hpre hX hs hget
  have hLen : k < (X.tr h).length := PTX.len_of_get hget
  exact elapsed_closing_order_of_lane hpre hX hs hscope
    (fun hClose => softmax_load_wait_before_gate hpre hX hs hClose hwait hstate hsite)
    hGate (by omega) hj hLen (by
      rintro ⟨i, et, hx⟩
      obtain ⟨p, _, hp⟩ := softmax_load_wait_exit_has_gate hpre hX hs hstate hsite hwait hx
      exact ⟨p, _, hp⟩)

theorem sourceLive_of_score_wait (hsite : d.site = .scoreWait) (horder : ld < wait)
    (hwait : X.get (g, wait) = some ⟨tag, .tc .waitLd⟩) :
    TcMma.SourceLive L X source (g, ld) cell :=
  sourceLive_of_actual_load_wait hpre hX hs hload hstate (by rw [hsite]; decide) horder hwait
end

/-- At the actual mask boundary, both score loads are followed by the wait which guards their
allocation lifetime. The three-event gap covers even the second of the two loads. -/
theorem sourceLive_at_mask {g ld j : Nat} {d : Wg0.D} {reg : Nat}
    {cell : TcMma.Cell} {source : EvId}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) (hlen : j ≤ (X.tr g).length)
    (hload : TcMma.LoadCell L X (g, ld) reg cell) (hgap : ld + 3 ≤ j) :
    TcMma.SourceLive L X source (g, ld) cell := by
  obtain ⟨w, _, _, _, _, _, _, hj, _, _, _, _, _, _, _, hsw, hsSite, _, hwait⟩ :=
    Wg0ScoreEventHistory.waits_of_mask hpre hX hs hd hsite hlen
  exact sourceLive_of_score_wait hpre hX hs hload hsw hsSite (by omega) hwait

/-- In the actual tracked trace, each score register has the current block's final QK issue
as its Tensor Memory read source. -/
theorem final_qk_score_read_source_at {cta issuer j : Nat} {lane : Fin 128} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) j =
      some (some (.wg0 d)))
    (hsite : d.site = .maskRead) (hlen : j ≤ (X.tr (GemmRing.softmax L cta lane)).length)
    (part : Fin 2) (reg : Fin 32) :
    let g := GemmRing.softmax L cta lane
    let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val
    ∃ src ld words, ld + (4 - part.val) = j ∧
      Frame.stateAt (Machine.code P L) X issuer src = some (some (.mma ⟨.qkMma 15, d.block⟩)) ∧
      X.TLd (g, ld) (Wg0.scoreLoadColumn part) words .s32x32b ∧
      X.MmaIssue (issuer, src) Wg1Mma.tmemP (MmaDataTrace.qkOperands L issuer d.block 15)
        (MmaDataTrace.qkAccum 15) [0, 0, 0, 0] ∧
      TcMma.LoadCell L X (g, ld) reg.val cell ∧
      TcMma.ReadSource L X .ld (issuer, src) (g, ld) cell := by
  obtain ⟨src, ld, words, hIndex, hgap, hState, hcell, hLd, hIssue, _, hRead⟩ :=
    ScoreReadback.final_qk_score_source_at hpre hX hs hmma hd hsite hlen part reg
  exact ⟨src, ld, words, hIndex, hState, hLd, hIssue, hcell,
    hRead (sourceLive_at_mask hpre hX hs hd hsite hlen hcell hgap)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime

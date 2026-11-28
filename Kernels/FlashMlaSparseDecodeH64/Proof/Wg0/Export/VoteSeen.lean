-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.MustSeen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Lemmas.Kernel.UbLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PldEl
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # What a block has read when it votes

At the vote (pc 578) of a lane of warpgroup 0 the block in progress has an event at each of its
reading pcs: a score load of each half, the mask word, the exchange word, and at least two reads of
each peer pair (the chain gives one, the data machine's parity the second). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The peer reads of a pair are even in number** at an event of a lane of warpgroup 0 that is
no read of that pair. -/
theorem w0_pf_even (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hge : 103 ≤ e.pc)
    (hv : W0Valid P.scale ((X.tr g).take k)) (k0 : Nat) (hk0 : k0 < 8) (hnp : e.pc ≠ 477 + 5 * k0) :
    ((w0Scan ((X.tr g).take k)).2.filter fun e =>
      e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length % 2 = 0 := by
  obtain ⟨st, hst, hslot, hpre, hI, -⟩ :=
    followW hp hX hFw hw he hub (w0_scale_rd hp) hv k le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he hst hub
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e.pc = (thread P L g).pc (.inl b, n) := hpc'
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  obtain ⟨hIW, -⟩ := hI d rfl
  have hpar := hIW.par ⟨k0, hk0⟩
  simp only at hpar
  have : ¬ ((w0Pf (w0Scan ((X.tr g).take k)).2 k0).length % 2 = 1) := fun h => by
    have hs := (hpar.mp h).1
    have h3 : d.c.site.pc = e.pc := hpc'.symm
    rw [hs] at h3
    simp only [Wg0.Site.pc] at h3
    omega
  exact (by omega : ∀ n : Nat, ¬ n % 2 = 1 → n % 2 = 0) _ this

/-- **The block has read its words at the store of the exchange word and at the vote** (pcs 566
and 578): a load of each half (the low half at pc 280 or 283, the high half at pc 278 or 285), the
mask word (289), and at least two reads of each peer pair. -/
theorem w0_block_seen (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} (hal : LaneAlive X g k) (hw : warp L g < 4) {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 566 ∨ e.pc = 578)
    (hv : W0Valid P.scale ((X.tr g).take k)) :
    (∃ ev ∈ (w0Scan ((X.tr g).take k)).2, ev.pc = 280 ∨ ev.pc = 283) ∧
    (∃ ev ∈ (w0Scan ((X.tr g).take k)).2, ev.pc = 278 ∨ ev.pc = 285) ∧
    (∃ ev ∈ (w0Scan ((X.tr g).take k)).2, ev.pc = 289) ∧
    ∀ k0 < 8, 2 ≤ ((w0Scan ((X.tr g).take k)).2.filter fun e =>
      e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero =>
      exfalso
      exact Wg0.w0_not_first hp hX hFw he (hal 0 e he (by omega)) (by omega)
    | succ j => exact ⟨j, rfl⟩
  have hb : w0Body e.pc = true := by rcases hpc with h | h <;> rw [h] <;> decide
  obtain ⟨f, hf, hfp⟩ := w0_prev_pc hp hX hFw hw he (hal (j + 1) e he le_rfl) hb hv
  have hfpc : f.pc = 512 ∨ f.pc = 572 := by
    rcases hpc with h | h <;> rw [h] at hfp <;> simp [w0Prev] at hfp <;> omega
  have hfb : w0Body f.pc = true := by rcases hfpc with h | h <;> rw [h] <;> decide
  have hm := w0_must hp hX hFw hal hw hv j (by omega) f hf hfb (by omega)
  have hg : ∀ p, (p = 512 ∨ p = 572) → [280, 283] ∈ w0Must p ∧ [278, 285] ∈ w0Must p ∧
      [289] ∈ w0Must p ∧ ∀ k0 < 8, [477 + 5 * k0] ∈ w0Must p := by
    intro p hp'; rcases hp' with rfl | rfl <;> decide
  obtain ⟨g1, g2, g3, g4⟩ := hg _ hfpc
  refine ⟨?_, ?_, ?_, fun k0 hk0 => ?_⟩
  · obtain ⟨ev, h1, h2⟩ := hm [280, 283] g1
    exact ⟨ev, h1, by simpa using h2⟩
  · obtain ⟨ev, h1, h2⟩ := hm [278, 285] g2
    exact ⟨ev, h1, by simpa using h2⟩
  · obtain ⟨ev, h1, h2⟩ := hm [289] g3
    exact ⟨ev, h1, by simpa using h2⟩
  · obtain ⟨ev, h1, h2⟩ := hm _ (g4 k0 hk0)
    have h2' : ev.pc = 477 + 5 * k0 := by simpa using h2
    obtain ⟨i, hi, -⟩ := w0Scan_snd_idx h1
    have hik : i < j + 1 := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_take] at this
      omega
    have hget : X.get (g, i) = some ev := by
      rw [List.getElem?_take_of_lt hik] at hi
      exact hi
    obtain ⟨a, bs, el, hk, -⟩ := w0_pld_el hp hX hFw hw (Wg0.W0Valid.take_le hv (by omega))
      hk0 hget (hal i ev hget (by omega)) h2'
    have hmem : ev ∈ (w0Scan ((X.tr g).take (j + 1))).2.filter fun e =>
        e.pc = 477 + 5 * k0 && (w0RdVal e).isSome := by
      simp [List.mem_filter, h1, h2', w0RdVal, hk]
    have hpos := List.length_pos_of_mem hmem
    have hev := w0_pf_even hp hX hFw hw he (hal (j + 1) e he le_rfl)
      (by rcases hpc with h | h <;> omega) hv k0 hk0
      (by rcases hpc with h | h <;> omega)
    omega

/-- **The events of the block in progress are trace events** before the prefix. -/
theorem w0_block_events (X : Execution) (g k : Nat) :
    ∀ ev ∈ (w0Fin ((X.tr g).take k)).2, ∃ i, i < k ∧ X.get (g, i) = some ev := by
  intro ev hev
  rw [w0Fin_snd] at hev
  obtain ⟨i, hi, -⟩ := w0Scan_snd_idx hev
  have hik : i < k := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at this
    omega
  refine ⟨i, hik, ?_⟩
  rw [List.getElem?_take_of_lt hik] at hi
  exact hi

/-- A block with an event at a reading pc that reads has a last reading there. -/
theorem w0Last_some {α : Type} {f : Event → Option α} {pcs : List Nat} {seg : List Event}
    (h : ∃ ev ∈ seg, ev.pc ∈ pcs ∧ (f ev).isSome) : ∃ v, w0Last f pcs seg = some v := by
  obtain ⟨ev, hev, hpc, hs⟩ := h
  unfold w0Last
  have hne : (seg.filterMap fun e => if e.pc ∈ pcs then f e else none) ≠ [] := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    intro h0
    have : v ∈ seg.filterMap fun e => if e.pc ∈ pcs then f e else none :=
      List.mem_filterMap.mpr ⟨ev, hev, by simp [hpc, hv]⟩
    rw [h0] at this
    cases this
  exact ⟨_, List.getLast?_eq_some_getLast hne⟩

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

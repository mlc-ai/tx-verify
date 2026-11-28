-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VoteSeen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MaskWord
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SldCol
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SegEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VmKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerPairs
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemLoad
import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # The vote keeps warpgroup 0's trace valid

At the vote (pc 578) the block in progress has read every word (`w0_block_seen`), and the words
are the valid block's (`W0Early` of the trace before it): each field that was read differs from its
default, so it is the valid block's. The exchange word's reading is the previous event's
(`hpm`, from the clause of the exchange load). The vote changes only its own result. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The last load of a half among the block's events reads 32 words. -/
theorem w0Last_tc_len (hp : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hFw : Follow P L X) {pcs : List Nat} {seg : List Event} {K : Nat} (hal : LaneUbFree X g K)
    (hseg : ∀ ev ∈ seg, ∃ i, i < K ∧ X.get (g, i) = some ev)
    (hpcs : ∀ p ∈ pcs, p = 278 ∨ p = 280 ∨ p = 283 ∨ p = 285)
    (hex : ∃ ev ∈ seg, ev.pc ∈ pcs) :
    ∃ v, w0Last w0TcVals pcs seg = some v ∧ v.length = 32 := by
  obtain ⟨ev, hev, hpc⟩ := hex
  obtain ⟨i, hik, hi⟩ := hseg ev hev
  obtain ⟨a, vals, hk, -⟩ := wg0_sldKind hp hX hFw hi (hal.ne hik hi) (hpcs _ hpc)
  obtain ⟨v, hv⟩ := w0Last_some (f := w0TcVals) (seg := seg)
    ⟨ev, hev, hpc, by simp [w0TcVals, hk]⟩
  obtain ⟨ev', hev', hpc', hv'⟩ := w0Last_event hv
  obtain ⟨i', hik', hi'⟩ := hseg ev' hev'
  obtain ⟨a', vals', hk', -⟩ := wg0_sldKind hp hX hFw hi' (hal.ne hik' hi') (hpcs _ hpc')
  refine ⟨v, hv, ?_⟩
  have : w0TcVals ev' = some vals' := by simp [w0TcVals, hk']
  rw [this] at hv'
  obtain rfl := Option.some.inj hv'
  exact scoreLdLen hp hX hi' hk' (by simpa using hpcs _ hpc')

/-- The last mask word read of a block is a 32-bit word. -/
theorem w0Last_mask (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hw : warp L g < 4) {seg : List Event} {K : Nat} (hal : LaneUbFree X g K)
    (hseg : ∀ ev ∈ seg, ∃ i, i < K ∧ X.get (g, i) = some ev)
    (hex : ∃ ev ∈ seg, ev.pc = 289) :
    ∃ x : BitVec 64, w0Last w0RdVal [289] seg = some (.bits 32 x) := by
  have key : ∀ ev ∈ seg, ev.pc = 289 → ∃ x : BitVec 64, w0RdVal ev = some (.bits 32 x) := by
    intro ev hev hpc
    obtain ⟨i, hik, hi⟩ := hseg ev hev
    obtain ⟨a, bs, hk⟩ := wg0_vmKind hp hX hFw hi (hal.ne hik hi) hpc
    obtain ⟨pc, kd⟩ := ev
    simp only at hpc hk
    subst hpc hk
    obtain ⟨x, hx, -⟩ := valid_read_word hp hX hFw (hIn.mbar hp X hX hFw)
      (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.coord hp X hX hFw)
      (hal.mono hik.le) hi
      ⟨hw, by norm_num, by norm_num⟩
    exact ⟨x, by simp [w0RdVal, hx]⟩
  obtain ⟨ev, hev, hpc⟩ := hex
  obtain ⟨x0, hx0⟩ := key ev hev hpc
  obtain ⟨v, hv⟩ := w0Last_some (f := w0RdVal) (pcs := [289]) (seg := seg)
    ⟨ev, hev, by simp [hpc], by simp [hx0]⟩
  obtain ⟨ev', hev', hpc', hv'⟩ := w0Last_event hv
  obtain ⟨x, hx⟩ := key ev' hev' (by simpa using hpc')
  rw [hx] at hv'
  exact ⟨x, by rw [hv, ← Option.some.inj hv']⟩

/-- **A complete peer pair is not the default**: the first element read is a value of eight
bytes, or the zero word. -/
theorem w0_peer_ne_default (hp : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k k0 : Nat}
    (hv : W0Valid P.scale ((X.tr g).take k)) (hk0 : k0 < 8)
    (hn2 : 2 ≤ ((w0Scan ((X.tr g).take k)).2.filter fun e =>
      e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length) (hal : LaneUbFree X g k) :
    (w0Words (w0Fin ((X.tr g).take k)).2).pw k0 ≠ (.pred false, .pred false) := by
  obtain ⟨j0, j1, x, y, a0, b0, a1, b1, hj0, hj1, hx, hy, -, -, hkx, hky, hpx, hpy, hw0, hw1,
    hpeer⟩ := w0_peer_events hp hX hFw hw hv hk0 (Nat.le_succ k) hn2 hal
  have hpw : (w0Words (w0Fin ((X.tr g).take k)).2).pw k0 =
      w0Peer (w0Fin ((X.tr g).take k)).2 k0 := by simp [w0Words, hk0]
  rw [hpw, hpeer]
  intro h
  have h1 := congrArg Prod.fst h
  simp only at h1
  obtain ⟨pc, kd⟩ := x
  simp only at hkx
  subst hkx
  have hlen : b0.length = 8 := by
    have := (hX.rf (.thread (g, j0)) a0 b0 (Or.inl ⟨pc, hx⟩)).1
    rw [this]; exact hw0.2
  simp only [w0A0] at h1
  cases hr : rebuild 3 b0 with
  | error f => simp [hr, Except.toOption] at h1
  | ok v =>
    have hb := PTX.Proof.rebuild_bytes_eq_length 3 b0 v hr
    rw [hlen] at hb
    simp only [hr, Except.toOption, Option.getD_some] at h1
    subst h1
    simp [Value.bytes] at hb

/-- **The block's words at the exchange store and at the vote agree with a valid block** on the
high half, the mask word and the peer pairs (they were read: `w0_block_seen`), and on the low
half and the exchange word where those were read (`W0Early`). -/
theorem w0_early_agree (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hw : warp L g < 4) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 566 ∨ e.pc = 578) (h : W0Valid P.scale
    ((X.tr g).take k)) :
    ∃ w' : W0Words, W0Ok P.scale w' ∧
      ((w0Words (w0Fin ((X.tr g).take k)).2).lo = [] ∨
        (w0Words (w0Fin ((X.tr g).take k)).2).lo = w'.lo) ∧
      (w0Words (w0Fin ((X.tr g).take k)).2).hi = w'.hi ∧
      (w0Words (w0Fin ((X.tr g).take k)).2).mw = w'.mw ∧
      (∀ k0 < 8, (w0Words (w0Fin ((X.tr g).take k)).2).pw k0 = w'.pw k0) ∧
      ((w0Words (w0Fin ((X.tr g).take k)).2).pm = .pred false ∨
        (w0Words (w0Fin ((X.tr g).take k)).2).pm = w'.pm) := by
  have hal := noUbBefore_of_get hX he
  obtain ⟨hlo, hhi, hmw, hpw⟩ := w0_block_seen hp hX hFw (LaneAlive.of_get hal he hub) hw he hpc h
  have hfs : (w0Scan ((X.tr g).take k)).2 = (w0Fin ((X.tr g).take k)).2 := (w0Fin_snd _).symm
  have hseg := w0_block_events X g k
  rw [hfs] at hlo hhi hmw
  obtain ⟨w', hw', e_lo, e_hi, e_mw, e_pw, e_pm⟩ : ∃ w' : W0Words, W0Ok P.scale w' ∧
      ((w0Words (w0Fin ((X.tr g).take k)).2).lo = [] ∨
        (w0Words (w0Fin ((X.tr g).take k)).2).lo = w'.lo) ∧
      ((w0Words (w0Fin ((X.tr g).take k)).2).hi = [] ∨
        (w0Words (w0Fin ((X.tr g).take k)).2).hi = w'.hi) ∧
      ((w0Words (w0Fin ((X.tr g).take k)).2).mw = .pred false ∨
        (w0Words (w0Fin ((X.tr g).take k)).2).mw = w'.mw) ∧
      (∀ k0 < 8, (w0Words (w0Fin ((X.tr g).take k)).2).pw k0 = (.pred false, .pred false) ∨
        (w0Words (w0Fin ((X.tr g).take k)).2).pw k0 = w'.pw k0) ∧
      ((w0Words (w0Fin ((X.tr g).take k)).2).pm = .pred false ∨
        (w0Words (w0Fin ((X.tr g).take k)).2).pm = w'.pm) := by
    rcases h.early with h0 | h1
    · obtain ⟨ev, hev, -⟩ := hlo
      rw [h0] at hev
      cases hev
    · exact h1
  refine ⟨w', hw', e_lo, ?_, ?_, fun k0 hk0 => ?_, e_pm⟩
  · refine e_hi.resolve_left fun h0 => ?_
    obtain ⟨v, hv, hl⟩ := w0Last_tc_len hp hX hFw hal hseg (pcs := [278, 285])
      (by intro p hp'; simp at hp'; omega)
      (by obtain ⟨ev, hev, hc⟩ := hhi; exact ⟨ev, hev, by simpa using hc⟩)
    simp only [w0Words, hv, Option.getD_some] at h0
    rw [h0] at hl
    cases hl
  · refine e_mw.resolve_left fun h0 => ?_
    obtain ⟨x, hx⟩ := w0Last_mask hp hIn hX hFw hw hal hseg hmw
    simp only [w0Words, hx, Option.getD_some] at h0
    cases h0
  · exact (e_pw k0 hk0).resolve_left (w0_peer_ne_default hp hX hFw hw h hk0 (hpw k0 hk0) hal)

/-- **The vote keeps the trace valid.** `hpm` is the exchange word's reading (the clause of the
event before the vote): it differs from the default. -/
theorem w0Valid_snoc_vote (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u)
    (hw : warp L g < 4) (hpc : e.pc = 578)
    (hpm : (w0Words (w0Fin ((X.tr g).take k)).2).pm ≠ .pred false)
    (h : W0Valid P.scale ((X.tr g).take k)) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  rw [trace_take_succ he]
  have hal := noUbBefore_of_get hX he
  obtain ⟨hlo, hhi, hmw, hpw⟩ := w0_block_seen hp hX hFw (LaneAlive.of_get hal he hub) hw he
    (Or.inr hpc) h
  have hfs : (w0Scan ((X.tr g).take k)).2 = (w0Fin ((X.tr g).take k)).2 := (w0Fin_snd _).symm
  have hseg := w0_block_events X g k
  rw [hfs] at hlo hhi hmw
  refine w0Core_vote hpc ?_ ?_ ?_ (fun k0 hk0 => w0_peer_ne_default hp hX hFw hw h hk0
    (hpw k0 hk0) hal) hpm h
  · obtain ⟨v, hv, hl⟩ := w0Last_tc_len hp hX hFw hal hseg (pcs := [280, 283])
      (by intro p hp'; simp at hp'; omega)
      (by obtain ⟨ev, hev, hc⟩ := hlo; exact ⟨ev, hev, by simpa using hc⟩)
    simp only [w0Words, hv, Option.getD_some]
    intro h0
    rw [h0] at hl
    cases hl
  · obtain ⟨v, hv, hl⟩ := w0Last_tc_len hp hX hFw hal hseg (pcs := [278, 285])
      (by intro p hp'; simp at hp'; omega)
      (by obtain ⟨ev, hev, hc⟩ := hhi; exact ⟨ev, hev, by simpa using hc⟩)
    simp only [w0Words, hv, Option.getD_some]
    intro h0
    rw [h0] at hl
    cases hl
  · obtain ⟨x, hx⟩ := w0Last_mask hp hIn hX hFw hw hal hseg hmw
    simp only [w0Words, hx, Option.getD_some]
    intro h0
    cases h0

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

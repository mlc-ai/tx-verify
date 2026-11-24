-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MaskReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingThreads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWordsHistory

@[expose] public section

/-! # The bits of the actual shared validity word -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX Protocol IndexRingThreads

/-- The index validity of one logical slot, including the selected cache and padding. -/
def gatheredValid (P : Params) (L : Launch) (g block pos : Nat) : Bool :=
  Wg1Tma.validBit P L g block (pos / 2) (pos % 2)

private def packedBytes : List Nat → Nat
  | [] => 0
  | b :: rest => b + 256 * packedBytes rest

private theorem packedBytes_bit (xs : List Nat) (hb : ∀ n ∈ xs, n < 256) (i : Nat) :
    (packedBytes xs).testBit i = (xs[i / 8]?.getD 0).testBit (i % 8) := by
  induction xs generalizing i with
  | nil => simp [packedBytes]
  | cons x xs ih =>
    have hx : x < 2 ^ 8 := hb x (by simp)
    rw [packedBytes, Nat.add_comm, Nat.testBit_two_pow_mul_add _ hx]
    by_cases h : i < 8
    · rw [ite_eq_left h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
      have hmod : i % 8 = (i - 8) % 8 := by omega
      rw [ite_eq_right h, ih (fun n hn => hb n (List.mem_cons_of_mem x hn)), hdiv, hmod]
      rfl

private theorem laneMask_bit (P : Params) (L : Launch) (g b lane i : Nat) (hi : i < 2) :
    (Wg1Index.laneMask P L g b lane).testBit i = Wg1Index.validBit P L g b lane i := by
  interval_cases i <;>
    cases h0 : Wg1Index.validBit P L g b lane 0 <;>
    cases h1 : Wg1Index.validBit P L g b lane 1 <;>
    simp [Wg1Index.laneMask, h0, h1] <;> decide

private theorem laneByte_bit (P : Params) (L : Launch) (g b q m i : Nat) (hm : m < 4) :
    (Wg1Index.laneByte P L g b (4 * q + m)).testBit i =
      if i / 2 = m then Wg1Index.validBit P L g b (4 * q + m) (i % 2) else false := by
  have hrem : (4 * q + m) % 4 = m := by omega
  rw [Wg1Index.laneByte, hrem, Nat.testBit_mul_two_pow]
  by_cases hl : 2 * m ≤ i
  · simp only [hl, decide_true, Bool.true_and]
    by_cases h : i - 2 * m < 2
    · have hq : i / 2 = m := by omega
      have hp : i - 2 * m = i % 2 := by omega
      rw [laneMask_bit P L g b _ _ h, ite_eq_left hq, hp]
    · have hq : i / 2 ≠ m := by omega
      rw [ite_eq_right hq]
      apply Nat.testBit_lt_two_pow
      have hmask := Wg1Index.laneMask_le P L g b (4 * q + m)
      have hpow : 2 ^ 2 ≤ 2 ^ (i - 2 * m) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · have hq : i / 2 ≠ m := by omega
    simp [hl, hq]

private theorem quadByte_bit (P : Params) (L : Launch) (g b q i : Nat) (hi : i < 8) :
    (Wg1Index.quadByte P L g b (4 * q)).testBit i =
      Wg1Index.validBit P L g b (4 * q + i / 2) (i % 2) := by
  have hx : i / 2 = 0 ∨ i / 2 = 1 ∨ i / 2 = 2 ∨ i / 2 = 3 := by omega
  have h0 := laneByte_bit P L g b q 0 i (by decide)
  have h1 := laneByte_bit P L g b q 1 i (by decide)
  have h2 := laneByte_bit P L g b q 2 i (by decide)
  have h3 := laneByte_bit P L g b q 3 i (by decide)
  simp only [Nat.add_zero] at h0
  simp only [Wg1Index.quadByte, Nat.testBit_or, h0, h1, h2, h3]
  rcases hx with h | h | h | h <;> simp [h]

private theorem producer_valid {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (g : Nat) (p : Fin 32) (b l t : Nat) :
    Wg1Index.validBit P L (producerThread L (ctaOf L g) p) b l t =
      Wg1Tma.validBit P L g b l t := by
  have he : ctaOf L (producerThread L (ctaOf L g) p) = ctaOf L g := by
    have hp := p.isLt
    simp only [producerThread, ctaOf, hpre.block]
    omega
  simp only [Wg1Index.validBit, Wg1Tma.validBit, Wg1Index.slotIdx, Wg1Tma.slotIdx,
    Wg1Index.eOf, Wg1Index.qOf, Wg1Tma.eOf, Wg1Tma.qOf, ctaidX, ctaidY, he]

variable {P : Params}

/-- Each bit of a followed softmax lane's published 32-bit mask names its logical sparse slot. -/
theorem maskWord_bit {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (g block : Nat) (i : Fin 32) :
    (MaskReadback.maskWord P L g block).toNat.testBit i.val =
      gatheredValid P L g block (32 * Wg0.half L g + i.val) := by
  let byte (k : Fin 4) := MaskReadback.maskByte P L g block k
  let xs := [byte 0, byte 1, byte 2, byte 3]
  have hb (b : Nat) (h : b ∈ xs) : b < 256 := by
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact Wg1Index.quadByte_lt P L _ _ _
  change ((BitVec.ofNat 64 (packedBytes xs)).toNat).testBit i.val = _
  rw [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, decide_eq_true (show i.val < 64 by omega),
    Bool.true_and, packedBytes_bit xs hb]
  let n : Fin 4 := ⟨i.val / 8, by omega⟩
  have hIndex (k : Fin 4) : xs[k.val]?.getD 0 = byte k := by
    fin_cases k <;> rfl
  rw [show i.val / 8 = n.val from rfl, hIndex n]
  let q := 4 * Wg0.half L g + n.val
  let p : Fin 32 := ⟨4 * (q % 8), by have := Nat.mod_lt q (by decide : 0 < 8); omega⟩
  change (Wg1Index.quadByte P L (producerThread L (ctaOf L g) p) block (4 * q)).testBit
    (i.val % 8) = _
  rw [quadByte_bit _ _ _ _ _ _ (by omega), producer_valid hpre]
  unfold gatheredValid
  have hPos : 4 * q + i.val % 8 / 2 = (32 * Wg0.half L g + i.val) / 2 := by
    dsimp [q, n]
    omega
  have hBit : i.val % 8 % 2 = (32 * Wg0.half L g + i.val) % 2 := by omega
  rw [hPos, hBit]

/-- The logical validity is independent of the observing lane in the same CTA. -/
theorem gatheredValid_same_cta {L : Launch} {g h block pos : Nat} (hc : ctaOf L g = ctaOf L h) :
    gatheredValid P L g block pos = gatheredValid P L h block pos := by
  simp only [gatheredValid, Wg1Tma.validBit, Wg1Tma.slotIdx, Wg1Tma.eOf, Wg1Tma.qOf,
    ctaidX, ctaidY, hc]

/-- The mask recorded by an actual WG0 exchange selects exactly the logical valid slots. -/
theorem exchange_mask_bit {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : Wg0.ScoreExchangeSite d.site) (bit : Fin 32) :
    d.maskWord.toNat.testBit bit.val =
      gatheredValid P L g d.block (32 * Wg0.half L g + bit.val) := by
  let limit := min i (X.tr g).length
  have hBound : limit ≤ (X.tr g).length := Nat.min_le_right _ _
  have hAt : Frame.stateAt (Machine.code P L) X g limit = some (some (.wg0 d)) := by
    by_cases h : i ≤ (X.tr g).length
    · simpa only [limit, Nat.min_eq_left h] using hd
    · have hle : (X.tr g).length ≤ i := by omega
      rw [Frame.stateAt_of_le hle] at hd
      simpa only [limit, Nat.min_eq_right hle] using hd
  obtain ⟨j, q, e, a, bs, _, hState, he, hMask, hBlock, _, _, hk, hWord⟩ :=
    Wg0.mask_event_before_exchange hBound hAt hsite
  have hEq := MaskReadback.rebuild_mask_exact hpre hX hs ht he hState hMask hk
  have hWordEq := (Value.bits.inj (Except.ok.inj (hWord.symm.trans hEq))).2
  rw [hWordEq, hBlock]
  exact maskWord_bit hpre g q.block bit

/-- The four-byte mask load precedes the causal cutoff since an eight-byte peer load
intervenes between them. This is valid even if the cutoff itself is an element of a vector. -/
theorem exchange_mask_bit_of_peer_read {L : Launch} {mem0 : Mem0} {X : Execution} {g i cut : Nat}
    {d : Wg0.D} {grp : Fin 8} {a : Acc} {bytes : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hr : X.Reads (g, i) a bytes)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead grp) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ MachineTracking.Dismisses P L X t)
    (bit : Fin 32) :
    d.maskWord.toNat.testBit bit.val =
      gatheredValid P L g d.block (32 * Wg0.half L g + bit.val) := by
  obtain ⟨j, q, e, fp, bs, hj, hState, he, hMask, hBlock, _, _, hk, hWord⟩ :=
    Wg0.mask_event_before_exchange (PTX.len_of_get hr.choose_spec).le hd
      (by rw [hsite]; trivial)
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hState
  obtain ⟨fp', _, hk', hSize, _, _⟩ := Wg0.composed_mask_footprint hpre hMask hf ⟨fp, bs, hk⟩
  have hfSize : fp.size = 4 := by rw [(Kind.rd.inj (hk.symm.trans hk')).1]; exact hSize
  obtain ⟨_, haSize, _, _⟩ := Wg0PeerWrites.read_geometry hpre hX hs hr hd hsite
  have hE : (X.get (g, j)).bind Event.acc = some fp := by
    rw [he]
    obtain ⟨tag, kind⟩ := e
    change kind = _ at hk
    rw [hk]
    rfl
  have hR : (X.get (g, i)).bind Event.acc = some a := by rw [hr.choose_spec]; rfl
  have hOrder : baseCausality L X (g, j) (g, cut) := by
    refine .single (.inl ⟨rfl, hj.trans_le hCut, hLen, ?_⟩)
    intro hSame
    have hFit : i - j ≤ cut - j := Nat.sub_le_sub_right hCut _
    have hEq := hSame.2 (i - j) hFit
    change (X.get (g, j + (i - j))).bind Event.acc =
      ((X.get (g, j)).bind Event.acc).map (Acc.shift (i - j)) at hEq
    rw [Nat.add_sub_of_le hj.le, hR, hE, Option.map_some] at hEq
    have hSizes := congrArg Acc.size (Option.some.inj hEq)
    change a.size = fp.size at hSizes
    omega
  have hEq := MaskReadback.rebuild_actual_mask hpre hX hs he hState hMask
    (fun t ht => hPrior t (ht.trans hOrder)) hk
  have hWordEq := (Value.bits.inj (Except.ok.inj (hWord.symm.trans hEq))).2
  rw [hWordEq, hBlock]
  exact maskWord_bit hpre g q.block bit

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

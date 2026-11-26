-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.GatherSlotProof
public import Lemmas.Kit.IntBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Loads
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.GatherBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RawBytes

@[expose] public section

/-! # The dequantizer's data is valid

`dq_valid`: every raw word and scale element a lane of warps 8-11 loads is valid data
(`DqValid`, `Iface/DqValue.lean`): the raw word's eight bytes are e4m3 bytes other than NaN and
the scale element's four bytes are below 255. Each byte a load reads is the byte its use's
gather wrote (`raw_read_byte`), which is the zero fill (value `0`) or byte `4 x + z` of the
physical row of a selected slot (`gather_byte`, with `GatherRowsGood`), a byte of the cache
that `Pre` makes e4m3 (`e4m3Ok`, columns below 512) or ue8m0 (`ue8m0Ok`, columns 512 to 527)
valid. The eight (four) bytes assemble to the word of their values (`rebuild_ints`). -/

/-! # The rows of every gather are good

`gather_rows_good` is the weak form of `gather_slot` (`GatherSlotProof.lean`): a row word that is
`-1` or the row of the selected slot of the block names a selected slot of the gather's cache, of
the lane's CTA. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every gather's coordinate words are good.** -/
theorem gather_rows_good (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : CoordInputs L X) : GatherRowsGood P L X := by
  intro g k pc a s he hat
  obtain ⟨q, -, r, -, -, h0, hmap, ys, hys, hys'⟩ :=
    gather_slot hp hX hFw hR hI hB hN he hat
  obtain ⟨hxlt, hylt⟩ := ctaid_lt hp g
  refine ⟨h0, ys, hys, fun i => ?_⟩
  rcases (hys' i).1 with h | ⟨hv, hrow⟩
  · exact .inl h
  · exact .inr ⟨ctaidY L g, hylt, ctaidX L g, hxlt, _, _, hv, hmap, hrow⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.Kit

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The word a load of `n` integer bytes reads is the word of their values. -/
theorem readWord_ints {n : Nat} (hn : n = 4 ∨ n = 8) {pc : Nat} {a : Acc}
    {bs : List (Option Byte)} {c : Nat → Nat} (hl : bs.length = n)
    (h : ∀ i < n, ∃ o, bs[i]? = some o ∧ c i < 256 ∧ IntClass o (c i)) :
    ∃ y, readWord (8 * n) ⟨pc, .rd a bs⟩ = some y ∧ ∀ i < n, y / 256 ^ i % 256 = c i := by
  obtain ⟨y, hr, hlt, hdig⟩ := rebuild_ints hn hl h
  refine ⟨y, ?_, hdig⟩
  rcases hn with rfl | rfl
  · norm_num at hlt
    simp only [readWord, hr, Except.toOption, Option.bind_some, bitsWord, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by norm_num; omega)]
    simp only [Nat.reduceMul, true_and, ite_eq_left_iff, not_lt]
    intro h; omega
  · norm_num at hlt
    simp only [readWord, hr, Except.toOption, Option.bind_some, bitsWord, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by norm_num; omega)]
    simp only [Nat.reduceMul, true_and, ite_eq_left_iff, not_lt]
    intro h; omega

/-- **The value of a byte a dequantizer load reads**: a cache byte of a selected slot, or the zero
fill. -/
private theorem byte_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : RawInputs L X) (hnu : NoUbInner L X) (hNc : CoordInputs L X) {g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hat : MbarRow.DequantAt L g pc) {i : Nat} (hi : i < a.size) :
    ∃ c < 256, (∃ o, bs[i]? = some o ∧ IntClass o c) ∧
      (a.size = 8 → c ≠ 127 ∧ c ≠ 255) ∧ (a.size = 4 → c < 255) := by
  have hG : GatherRowsGood P L X := gather_rows_good hp hX hFw hR hI hB hNc
  obtain ⟨gi, ki, pcg, al, s, o, x, y, z, byte, hget, hat', ho, hn, hx, hy, hz, h8, h4, -, hwb,
    hbs, -⟩ := raw_read_byte hp hX hFw hR hI hB hN hnu he hat hi
  obtain ⟨byte', hwb', hcls⟩ := gather_byte hp hX hFw hnu hG hget hat' ho hn hx hy hz
  obtain rfl : byte' = byte := by rw [hwb] at hwb'; exact (Option.some.inj hwb').symm
  rcases hcls with rfl | ⟨e, he', q, hq, extra, j, hv, rfl⟩
  · exact ⟨0, by omega, ⟨_, hbs, .inr ⟨rfl, z, hz, rfl⟩⟩, fun _ => ⟨by omega, by omega⟩,
      fun _ => by omega⟩
  · have hlt : cacheByte P extra (slotRow P e q extra j) (4 * x + z) < 256 := by
      cases extra
      · exact (P.kvByte _ _).isLt
      · exact (P.extraKvByte _ _).isLt
    have hrb : rowBytes P e q extra j (4 * x + z) =
        cacheByte P extra (slotRow P e q extra j) (4 * x + z) := by cases extra <;> rfl
    refine ⟨_, hlt, ⟨_, hbs, .inl rfl⟩, fun h => ?_, fun h => ?_⟩
    · have := hp.e4m3Ok e he' q hq extra j hv (4 * x + z) (h8 h)
      rw [hrb] at this
      omega
    · have := hp.ue8m0Ok e he' q hq extra j hv (32 * (4 * x + z - 512)) (by have := h4 h; omega)
      have hdiv : 512 + 32 * (4 * x + z - 512) / 32 = 4 * x + z := by have := h4 h; omega
      rw [hdiv, hrb] at this
      omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
  (hnu : NoUbInner L X) (hNc : CoordInputs L X)
include hp hX hFw hR hI hB hN hnu hNc

/-- **Valid data**: every raw word and scale element a dequantizer lane reads before its event
`k` is valid (`DqValid`), when no event of lane `g` before `k` and no event of warps 0 to 3 is
undefined behaviour. -/
theorem dq_valid (g k : Nat) (hk : NoUbBefore X g k) : DqValid X g k := by
  intro j hj e he
  obtain ⟨pc, kind⟩ := e
  have hub : ∀ f, kind ≠ .ub f := hk.ne hj he
  constructor
  · intro r s hr hs hpc
    obtain ⟨hat, a, bs, hk, hsz⟩ := dequant_raw_load hp hX hFw he hub hr hs hpc
    subst hk
    have hlen : bs.length = 8 := by
      have := (hX.rf (.thread (g, j)) a bs (Or.inl ⟨pc, he⟩)).1
      omega
    choose! c hc using fun i (hi : i < 8) =>
      byte_value hp hX hFw hR hI hB hN hnu hNc he hat (i := i) (by omega)
    obtain ⟨y, hy, hdig⟩ := readWord_ints (n := 8) (Or.inr rfl) (pc := pc) (a := a) hlen
      fun i hi => by
        obtain ⟨hlt, ⟨o, ho, hcl⟩, -, -⟩ := hc i hi
        exact ⟨o, ho, hlt, hcl⟩
    refine ⟨y, hy, fun i hi => ?_⟩
    rw [hdig i hi]
    obtain ⟨-, -, h8, -⟩ := hc i hi
    exact h8 hsz
  · intro r hr hpc
    obtain ⟨hat, a, bs, hk, hsz⟩ := dequant_scale_load hp hX hFw he hub hr hpc
    subst hk
    have hlen : bs.length = 4 := by
      have := (hX.rf (.thread (g, j)) a bs (Or.inl ⟨pc, he⟩)).1
      omega
    choose! c hc using fun i (hi : i < 4) =>
      byte_value hp hX hFw hR hI hB hN hnu hNc he hat (i := i) (by omega)
    obtain ⟨y, hy, hdig⟩ := readWord_ints (n := 4) (Or.inl rfl) (pc := pc) (a := a) hlen
      fun i hi => by
        obtain ⟨hlt, ⟨o, ho, hcl⟩, -, -⟩ := hc i hi
        exact ⟨o, ho, hlt, hcl⟩
    refine ⟨y, hy, fun i hi => ?_⟩
    rw [hdig i hi]
    obtain ⟨-, -, -, h4⟩ := hc i hi
    exact h4 hsz

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherSlot
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqValid
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.GatherBytes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.GatherSlotProof
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.LoadLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Loads
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.ScaleBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RawBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.GatherBlkUse
import Lemmas.Kit.IntBytes

@[expose] public section

/-! # The value a chunk store dequantizes

`dq_store_slot`: the number `e4m3Val (byte j of the raw word) * ue8m0Val (scale byte 2 s + hi)` a
chunk store `(r, s)` of lane `h` into tile `bw` at use `u` computes (`dq_b_elem`) is, when the slot
at position `R = h % 128 / 8 + 16 r` of block `2 u + bw` is valid, the dequantized value
`e4m3Val (row F) * ue8m0Val (row (512 + F / 32))` of feature `F = 64 s + 8 (h % 8) + j` of that
slot's cache row (the last raw load and the last four scale loads are the store's block's:
`dequant_store_loads`; their words' digits are the row's bytes: `dq_load_digits`). -/

/-! # The word a dequantizer load reads is the row's bytes

A raw load (eight bytes) or a scale element load (four bytes) of a dequantizer lane reads a word
`y` (`readWord`) whose digit `i` is byte `c0 + i` of the cache row of the slot at position `R` of
the block `2 v + b` (`rowBytes`), when that slot is valid (`dq_load_digits`): each byte is the
slot's cache byte (`raw_byte_slot`), the digits of the rebuilt word are the bytes' values
(`rebuild_ints`). -/

/-! # The slot a raw byte belongs to

A byte a dequantizer lane loads from raw tile `b` at use `v`, tile row `R`, tile column `c0 + i`
(`dequant_rd`), is a byte of the gather `R / 4` of block `r = 2 v + b`, row `R % 4` of its box
(`raw_read_byte`, `tma_gatherBlkUse`: the shared byte is `2304 (R / 4) + 576 (R % 4) + 36864 b`
above the raw region). With `GatherSlot` the row word of that row is `-1` (the byte is the zero
fill) or the row of the selected slot at position `R` of block `r` (`w0BlockSlot`), the byte
`c0 + i` of that cache row (`raw_byte_slot`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow TensorDescriptor

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem gpc_inj {a b : Nat} (_ha : a < 16) (_hb : b < 16)
    (h : gatherPc a = gatherPc b) : a = b := by
  simp only [gatherPc] at h
  split_ifs at h <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
  (hnu : NoUbInner L X) (hNc : CoordInputs L X)
include hp hX hFw hR hI hB hN hnu hNc

/-- **The slot of a byte a dequantizer lane loads from a raw tile**: block `r = 2 v + b`, the
tile row `R` is position `R` of the block; the byte is byte `c0 + i` of the row of the slot
when it is selected, and the zero fill (`z = (c0 + i) % 4`) when it is not. -/
theorem raw_byte_slot {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.DequantAt L g pc) {i : Nat}
    (hi : i < a.size) :
    ∃ (b : Fin 2) (v R c0 : Nat) (byte : Byte), R < 64 ∧
      a.loc.addr = L.sharedBase + (Region.raw b).lo + (576 * R + c0) ∧ c0 + a.size ≤ 528 ∧
      (a.size = 8 → c0 + 8 ≤ 512) ∧ (a.size = 4 → 512 ≤ c0) ∧
      okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
      bs[i]? = some (some byte) ∧
      (slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) →
        byte = rowByte P (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (slotRow P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
            (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R)) (c0 + i)) ∧
      (¬ slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) →
        byte = (.bits 32 0, (c0 + i) % 4)) := by
  obtain ⟨gi, ki, pcg, al, s, o, x, y, z, byte, hget, hat', ho, hn, hx, hy, hz, -, -, hwl, hwb,
    hbs, b, v, q, R, c0, hq, hsh, haddr, hc0, hr8, hr4, hv1, hcnt⟩ :=
    raw_read_byte hp hX hFw hR hI hB hN hnu he hat hi
  obtain ⟨hls, hlc, hlo, hhi⟩ := MemRow.SharedIn.locIn hsh (Acc.covers_at hi)
  obtain ⟨q1, hq1, r, hpc1, hcnt1, hmb1, hsb, hiss⟩ :=
    tma_gatherBlkUse hp hX hFw hget hat' (a := al) (s := s) rfl
  have hgw := gather_writeLoc hp hX hFw hget hat' (x := x) (y := y) (z := z) (by omega) hy hz
  rw [hsb] at hgw
  have hloc := Option.some.inj (hgw.symm.trans hwl)
  simp only [Loc.at, Loc.mk.injEq] at hloc
  simp only [Region.lo, Region.size, Loc.at] at hlo hhi haddr
  obtain ⟨-, hlcg, hladd⟩ := hloc
  have hcta : gi / L.block = g / L.block := by
    exact hlcg.trans hlc
  rw [hcta] at hmb1 hiss
  obtain ⟨q2, hq2, r2, hpc2, hcnt2, h0, hmap, ys, hys, hys'⟩ :=
    gather_slot hp hX hFw hR hI hB hNc hget hat'
  have hqq : q2 = q1 := gpc_inj hq2 hq1 (hpc2.symm.trans hpc1)
  subst hqq
  have hrr : r2 = r := by split_ifs at hcnt1 hcnt2 <;> omega
  subst hrr
  -- the address equations: the tile, the row and the column
  have hb2 : b.val = (MbarRow.slot2 r2).val := by
    simp only [MbarRow.slot2] at hladd ⊢
    omega
  have hRq : R = 4 * q2 + y := by omega
  have hbb : b = MbarRow.slot2 r2 := Fin.ext hb2
  have hcol : 4 * x + z = c0 + i := by omega
  have hu : ringUses 2 (MbarRow.slot2 r2).val r2 = r2 / 2 :=
    ringUses_here (by simp [MbarRow.slot2]) (MbarRow.slot2 r2).isLt
  subst hbb
  rw [hu] at hiss
  have hvq : v = r2 / 2 := by omega
  have hr2 : r2 = 2 * v + (MbarRow.slot2 r2).val := by simp only [MbarRow.slot2]; omega
  refine ⟨MbarRow.slot2 r2, v, R, c0, byte, by omega, haddr, hc0, hr8, hr4, hv1, hbs, ?_⟩
  rw [← hr2, hRq]
  have hcy : ctaidY L gi = ctaidY L g := by simp only [ctaidY, ctaOf, hcta]
  have hcx : ctaidX L gi = ctaidX L g := by simp only [ctaidX, ctaOf, hcta]
  rw [hcy, hcx] at hys'
  rw [hcy] at hmap
  obtain ⟨hw1, hw2⟩ := hys' ⟨y, hy⟩
  obtain rfl : o.spec = s := by
    obtain ⟨⟨addr, pc', hiss'⟩, -, -⟩ := hX.tensor _ o ho
    rw [hget] at hiss'
    obtain ⟨-, hk⟩ := Event.mk.inj (Option.some.inj hiss')
    exact (Kind.tensorIssue.inj hk).2.symm
  have hiss' : X.TensorIssue (gi, ki) al o.spec := ⟨pcg, hget⟩
  obtain ⟨hxlt, hylt⟩ := ctaid_lt hp g
  refine ⟨fun hv => ?_, fun hnv => ?_⟩
  · have hrow := hw2 hv
    have hex : w0BlockExtra P (ctaidY L g) r2 = true → P.extra_topk ≠ 0 := by
      intro hextra
      rw [hextra] at hv
      have hlen : _ < P.extraTopkLen (ctaidY L g) := hv.1
      have := extraLen_le hp hylt (e := ctaidY L g)
      omega
    have hlt := slotRow_lt hp hylt hxlt hv
    obtain ⟨byte', hw, -, hval⟩ := gather_byte_map hp hX hFw hnu _ hex hiss' ho hn hmap hys h0
      hx hy hz (.inr ⟨_, hrow, hlt⟩)
    obtain rfl : byte' = byte := Option.some.inj (hw.symm.trans hwb)
    rw [hval _ hrow hlt, hcol]
  · have h : ys ⟨y, hy⟩ = -1 := by
      rcases hw1 with h | ⟨hv, -⟩
      · exact h
      · exact absurd hv hnv
    obtain ⟨extra, hex, hD⟩ : ∃ extra : Bool, (extra = true → P.extra_topk ≠ 0) ∧
        (⟨o.spec.outer, o.spec.descriptor⟩ : Σ n, Descriptor n) = gatherMap P extra := by
      rcases gather_enc hp hX hFw hget hat' with h' | ⟨hne, h'⟩
      · exact ⟨false, (fun h => by cases h), h'⟩
      · exact ⟨true, fun _ => hne, h'⟩
    obtain ⟨byte', hw, hfill, -⟩ := gather_byte_map hp hX hFw hnu extra hex hiss' ho hn hD hys h0
      hx hy hz (.inl h)
    obtain rfl : byte' = byte := Option.some.inj (hw.symm.trans hwb)
    rw [hfill h]
    simp only [Prod.mk.injEq, true_and]
    omega

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow PTX.Kit

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem raw_addr_inj {base : Nat} {bA bB : Fin 2} {RA RB cA cB sz : Nat}
    (h : base + (Region.raw bA).lo + (576 * RA + cA) = base + (Region.raw bB).lo + (576 * RB + cB))
    (hRA : RA < 64) (hRB : RB < 64) (hcA : cA + sz ≤ 528) (hcB : cB + sz ≤ 528) :
    bA = bB ∧ RA = RB ∧ cA = cB := by
  simp only [Region.lo] at h
  have h1 := bA.isLt
  have h2 := bB.isLt
  refine ⟨Fin.ext ?_, ?_, ?_⟩ <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
  (hnu : NoUbInner L X) (hNc : CoordInputs L X)
include hp hX hFw hR hI hB hN hnu hNc

open Classical in
/-- **The word a dequantizer load reads** (raw word or scale element): at tile row `R`, column `c0`
of raw tile `b` at use `v`, and a word `y` whose digit `i` is byte `c0 + i` of the row of the
slot at position `R` of block `2 v + b` when that slot is valid. -/
theorem dq_load_digits {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.DequantAt L g pc)
    (hn : a.size = 4 ∨ a.size = 8) :
    ∃ (b : Fin 2) (v R c0 y : Nat), R < 64 ∧
      a.loc.addr = L.sharedBase + (Region.raw b).lo + (576 * R + c0) ∧ c0 + a.size ≤ 528 ∧
      okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
      readWord (8 * a.size) ⟨pc, .rd a bs⟩ = some y ∧
      (slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) →
        ∀ i < a.size, y / 256 ^ i % 256 =
          rowBytes P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
            (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) (c0 + i)) := by
  have hpos : 0 < a.size := by omega
  obtain ⟨b, v, R, c0, byte0, hR64, haddr, hc0, -, -, hpl, -⟩ :=
    raw_byte_slot hp hX hFw hR hI hB hN hnu hNc he hat (i := 0) hpos
  have hlen : bs.length = a.size := by
    have := (hX.rf (.thread (g, k)) a bs (Or.inl ⟨pc, he⟩)).1
    omega
  have hall : ∀ i < a.size, ∃ o, bs[i]? = some o ∧
      (if slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) then
        rowBytes P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) (c0 + i) else 0) < 256 ∧
      IntClass o (if slotValid P (ctaidY L g) (ctaidX L g)
          (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) then
        rowBytes P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) (c0 + i) else 0) := by
    intro i hi
    obtain ⟨b', v', R', c0', byte, hR', haddr', hc0', -, -, hpl', hbs, hval, hinv⟩ :=
      raw_byte_slot hp hX hFw hR hI hB hN hnu hNc he hat hi
    obtain ⟨rfl, rfl, rfl⟩ := raw_addr_inj (sz := a.size) (haddr.symm.trans haddr') hR64 hR' hc0
      hc0'
    obtain rfl : v = v' := by omega
    refine ⟨some byte, hbs, ?_⟩
    by_cases hv : slotValid P (ctaidY L g) (ctaidX L g)
        (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
        (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R)
    · have hrb : rowBytes P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R) (c0 + i) =
          cacheByte P (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
            (slotRow P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
              (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R)) (c0 + i) := by
        cases w0BlockExtra P (ctaidY L g) (2 * v + b.val) <;> rfl
      have hlt : cacheByte P (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
          (slotRow P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) (2 * v + b.val))
            (w0BlockSlot P (ctaidY L g) (2 * v + b.val) R)) (c0 + i) < 256 := by
        unfold cacheByte
        split_ifs
        · exact (P.extraKvByte _ _).isLt
        · exact (P.kvByte _ _).isLt
      simp only [hv, ↓reduceIte]
      rw [hrb]
      refine ⟨hlt, .inl ?_⟩
      rw [hval hv]
      rfl
    · simp only [hv, ↓reduceIte]
      obtain ⟨hz, -⟩ : byte = (.bits 32 0, (c0 + i) % 4) ∧ True := ⟨hinv hv, trivial⟩
      exact ⟨by omega, .inr ⟨rfl, (c0 + i) % 4, by omega, by rw [hz]⟩⟩
  obtain ⟨y, hy, hdig⟩ := readWord_ints (n := a.size) hn (pc := pc) (a := a) hlen hall
  refine ⟨b, v, R, c0, y, hR64, haddr, hc0, hpl, hy, fun hv i hi => ?_⟩
  rw [hdig i hi]
  simp only [hv, ↓reduceIte]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow Numeric.Dequant

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
  (hnu : NoUbInner L X) (hNc : CoordInputs L X)
include hp hX hFw hR hI hB hN hnu hNc

/-- **The number a chunk store computes is the slot's dequantized value** (valid data). -/
theorem dq_store_slot {h k u : Nat} {a : Acc} {bs : List Byte} {r s : Nat} (hr : r < 4)
    (hs : s < 8) (he : X.get (h, k) = some ⟨dqStorePc r s, .wr a bs⟩) (hv : DqValid X h k)
    {bw : Fin 2}
    (hws : MemRow.WsAcc L (h / L.block) ((Region.dequant bw).lo + MemRow.dqChunk (h % 128) r s)
      16 a)
    (hu : arrivals (mbarLoc L (h / L.block) (.dequantReady bw)) ((X.tr h).take k) = u) {j : Nat}
    (hj : j < 8) :
    slotValid P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) (2 * u + bw.val))
        (w0BlockSlot P (ctaidY L h) (2 * u + bw.val) (h % 128 / 8 + 16 * r)) →
      e4m3Val (byteAt (rawWordOf (lastAt X h k (dqRawPc r s) 1)) j) *
          ue8m0Val (byteAt (scaleWordOf (lastAt X h k (dqScalePc r) 4))
            (2 * s + if h % 8 < 4 then 0 else 1)) =
        slotValue P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) (2 * u + bw.val))
          (w0BlockSlot P (ctaidY L h) (2 * u + bw.val) (h % 128 / 8 + 16 * r))
          (64 * s + 8 * (h % 8) + j) := by
  intro hval
  obtain ⟨u0, hu0, hrp, ⟨kr, ar, bsr, hkr, hgr, hlast, hsz, haddr, hpl⟩, hlen4, hsc⟩ :=
    dequant_store_loads hp hX hFw hr hs he hv hws
  have hu0u : u0 = u := hu0.symm.trans hu
  subst hu0u
  have hr15 : h % 128 / 8 ≤ 15 := by omega
  have hh8 : h % 8 * 8 ≤ 56 := by omega
  -- the raw word
  have hubr : ∀ f, (⟨dqRawPc r s, .rd ar bsr⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨hatr, -⟩ := dequant_raw_load hp hX hFw hgr hubr hr hs rfl
  obtain ⟨b, v, R, c0, y, hR64, haddr', hc0, hpl', hy, hdig⟩ :=
    dq_load_digits hp hX hFw hR hI hB hN hnu hNc hgr hatr (Or.inr hsz)
  obtain ⟨hb, hRR, hcc⟩ := raw_addr_inj (sz := 8) (haddr'.symm.trans haddr) hR64
    (by omega) (by omega) (by omega)
  have hvu : v = u0 := by rw [hb] at hpl'; omega
  rw [hb, hvu, hRR, hcc] at hdig
  have hy' : readWord 64 ⟨dqRawPc r s, .rd ar bsr⟩ = some y := by rw [hsz] at hy; exact hy
  have hraw : rawWordOf (lastAt X h k (dqRawPc r s) 1) = y := by
    rw [hlast]; simp only [rawWordOf, hy', Option.getD_some]
  have hrawd := hdig hval j (by omega)
  -- the four scale words
  have scale_dig : ∀ jj < 4, ∀ kj aj bsj, X.get (h, kj) = some ⟨dqScalePc r, .rd aj bsj⟩ →
      aj.size = 4 → aj.loc.addr = L.sharedBase + (Region.raw bw).lo +
        (576 * (h % 128 / 8 + 16 * r) + (512 + 4 * jj)) →
      okPolls (mbarLoc L (h / L.block) (.rawReady bw)) ((X.tr h).take kj) = u0 + 1 →
      ∃ y, readWord 32 ⟨dqScalePc r, .rd aj bsj⟩ = some y ∧ y < 2 ^ 32 ∧
        (slotValid P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) (2 * u0 + bw.val))
          (w0BlockSlot P (ctaidY L h) (2 * u0 + bw.val) (h % 128 / 8 + 16 * r)) →
          ∀ i < 4, y / 256 ^ i % 256 =
            rowBytes P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) (2 * u0 + bw.val))
              (w0BlockSlot P (ctaidY L h) (2 * u0 + bw.val) (h % 128 / 8 + 16 * r))
              (512 + 4 * jj + i)) := by
    intro jj hjj kj aj bsj hg hsz4 hadr hp4
    have hubj : ∀ f, (⟨dqScalePc r, .rd aj bsj⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
    obtain ⟨hatj, -⟩ := dequant_scale_load hp hX hFw hg hubj hr rfl
    obtain ⟨b', v', R', c0', y', hR64', haddr2, hc02, hpl2, hy2, hdig2⟩ :=
      dq_load_digits hp hX hFw hR hI hB hN hnu hNc hg hatj (Or.inl hsz4)
    obtain ⟨hb2, hRR2, hcc2⟩ := raw_addr_inj (sz := 4) (haddr2.symm.trans hadr) hR64'
      (by omega) (by omega) (by omega)
    have hvu2 : v' = u0 := by rw [hb2] at hpl2; omega
    rw [hb2, hvu2, hRR2, hcc2] at hdig2
    rw [hsz4] at hy2 hdig2
    refine ⟨y', hy2, ?_, hdig2⟩
    exact readWord_lt32 hy2
  obtain ⟨k0, a0, bs0, hk0, hg0, hn0, hs0, hd0, hp0⟩ := hsc 0 (by omega)
  obtain ⟨k1, a1, bs1, hk1, hg1, hn1, hs1, hd1, hp1⟩ := hsc 1 (by omega)
  obtain ⟨k2, a2, bs2, hk2, hg2, hn2, hs2, hd2, hp2⟩ := hsc 2 (by omega)
  obtain ⟨k3, a3, bs3, hk3, hg3, hn3, hs3, hd3, hp3⟩ := hsc 3 (by omega)
  obtain ⟨y0, hy0, l0, hq0⟩ := scale_dig 0 (by omega) k0 a0 bs0 hg0 hs0 hd0 hp0
  obtain ⟨y1, hy1, l1, hq1⟩ := scale_dig 1 (by omega) k1 a1 bs1 hg1 hs1 hd1 hp1
  obtain ⟨y2, hy2, l2, hq2⟩ := scale_dig 2 (by omega) k2 a2 bs2 hg2 hs2 hd2 hp2
  obtain ⟨y3, hy3, l3, hq3⟩ := scale_dig 3 (by omega) k3 a3 bs3 hg3 hs3 hd3 hp3
  have hL : lastAt X h k (dqScalePc r) 4 = [⟨dqScalePc r, .rd a0 bs0⟩, ⟨dqScalePc r, .rd a1 bs1⟩,
      ⟨dqScalePc r, .rd a2 bs2⟩, ⟨dqScalePc r, .rd a3 bs3⟩] := by
    rcases hL : lastAt X h k (dqScalePc r) 4 with
      _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, l⟩⟩⟩⟩⟩ <;>
      simp only [hL, List.length_nil, List.length_cons, List.getElem?_cons_zero,
        List.getElem?_cons_succ] at hlen4 hn0 hn1 hn2 hn3 <;> try omega
    simp only [Option.some.injEq] at hn0 hn1 hn2 hn3
    rw [hn0, hn1, hn2, hn3]
  obtain ⟨wi, bi, hwi, hbi, hB⟩ : ∃ wi bi, wi < 4 ∧ bi < 4 ∧
      2 * s + (if h % 8 < 4 then 0 else 1) = 4 * wi + bi :=
    ⟨(2 * s + if h % 8 < 4 then 0 else 1) / 4, (2 * s + if h % 8 < 4 then 0 else 1) % 4,
      by split_ifs <;> omega, by omega, by omega⟩
  have hsc' : byteAt (scaleWordOf (lastAt X h k (dqScalePc r) 4)) (4 * wi + bi) =
      rowBytes P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) (2 * u0 + bw.val))
        (w0BlockSlot P (ctaidY L h) (2 * u0 + bw.val) (h % 128 / 8 + 16 * r))
        (512 + 4 * wi + bi) := by
    rw [hL, scaleWordOf_byte hy0 hy1 hy2 hy3 hwi hbi]
    interval_cases wi
    · exact hq0 hval bi hbi
    · exact hq1 hval bi hbi
    · exact hq2 hval bi hbi
    · exact hq3 hval bi hbi
  rw [hraw, hB]
  unfold slotValue dequant
  have hc8 : 8 * (h % 8) + j < 64 := by omega
  have hidx : 512 + (64 * s + 8 * (h % 8) + j) / 32 = 512 + 4 * wi + bi := by
    have : (64 * s + 8 * (h % 8) + j) / 32 = 2 * s + (if h % 8 < 4 then 0 else 1) := by
      split_ifs <;> omega
    omega
  rw [hidx, ← hsc']
  have hrj : rowBytes P (ctaidY L h) (ctaidX L h) (w0BlockExtra P (ctaidY L h) (2 * u0 + bw.val))
      (w0BlockSlot P (ctaidY L h) (2 * u0 + bw.val) (h % 128 / 8 + 16 * r))
      (64 * s + 8 * (h % 8) + j) = y / 256 ^ j % 256 := by
    rw [hrawd]; congr 1; omega
  rw [hrj]
  rfl

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

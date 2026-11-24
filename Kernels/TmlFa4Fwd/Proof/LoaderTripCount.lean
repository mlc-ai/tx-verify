-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
public import Kernels.TmlFa4Fwd.Flow.Code.Part006
public import Kernels.TmlFa4Fwd.Flow.Code.Part007

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- A nonnegative 31-bit word has its ordinary signed value. -/
theorem int32Signed {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The decoded upper-bit mask rounds a 32-bit word down to a block boundary. -/
theorem lowSevenMask {x : Nat} (hx : x < 2 ^ 32) :
    x &&& 4294967168 = x / 128 * 128 := by
  have hDiv : (x &&& 4294967168) / 128 = x / 128 := by
    rw [show 128 = 2 ^ 7 from rfl, Nat.and_div_two_pow]
    change x / 128 &&& (2 ^ 25 - 1) = x / 128
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  have hMod : (x &&& 4294967168) % 128 = 0 := by
    rw [show 128 = 2 ^ 7 from rfl, Nat.and_mod_two_pow]
    simp
  omega

private structure CeilSite where
  pc : Nat
  lengthReg : Nat
  quotient : Nat
  remainder : Nat
  count : Nat

private def ceilSite : Fin 3 → CeilSite
  | 0 => ⟨439, 1086, 1815, 114, 1818⟩
  | 1 => ⟨452, 1821, 1825, 117, 1828⟩
  | 2 => ⟨464, 1829, 1833, 120, 1836⟩

private theorem blockCount (site : Fin 3) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 31) :
    Seg kernel [] l g 10 (ceilSite site).pc [((ceilSite site).lengthReg, b32 len)]
      ((ceilSite site).pc + 10) [((ceilSite site).count, b32 ((len + 127) / 128))] := by
  have h32 : len < 2 ^ 32 := by omega
  have h64 : len < 2 ^ 64 := by omega
  have hx64 : len < 18446744073709551616 := h64
  have hDiv : len / 128 < 2 ^ 32 := by omega
  have hMask : len / 128 * 128 < 2 ^ 32 := by omega
  have shr31 : (len : Int) / 2 ^ 31 = 0 := by omega
  have shr7 : (len : Int) / 2 ^ 7 = (len / 128 : Nat) := by omega
  have s31 : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := rfl
  have s7 : min (truncBits 32 (BitVec.ofInt 64 7)).toNat 32 = 7 := rfl
  have s25 : (truncBits 32 (BitVec.ofInt 64 25)).toNat = 25 := rfl
  have z : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have z32 : truncBits 32 0 = 0 := rfl
  have zShift : (0 : BitVec 64) >>> 25 = 0 := rfl
  have h25 : ¬25 ≥ 32 := by decide
  have hNeg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hPos : (-1 : Int) < len := by omega
  have m32 : truncBits 32 (BitVec.ofInt 64 (-128)) = BitVec.ofNat 64 4294967168 := rfl
  have aZero : BitVec.ofNat 64 len + 0 = BitVec.ofNat 64 len := BitVec.add_zero _
  have hFirst : Seg kernel [] l g 8 (ceilSite site).pc [((ceilSite site).lengthReg, b32 len)]
      ((ceilSite site).pc + 8)
      [((ceilSite site).quotient, b32 (len / 128)),
       ((ceilSite site).remainder, .pred (decide (len ≠ len / 128 * 128)))] := by
    fin_cases site <;> intro t ht <;> seg_fp ht using
      simp only [b32, s31, s7, s25, ite_eq_right h25, shr31, shr7, z, z32, zShift,
        aZero, truncBits_ofNat h32 (by decide), m32,
        truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
        Option.getD_some, int32Signed hlen, hNeg, gt_iff_lt, hPos, decide_true, Bool.true_and,
        toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
      all_goals
        simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, lowSevenMask h32,
          truncBits_ofNat hMask (by decide),
          toNat_ofNat_lt (show len / 128 * 128 < 2 ^ 64 by omega)]
  have hLast : Seg kernel [] l g 2 ((ceilSite site).pc + 8)
      [((ceilSite site).quotient, b32 (len / 128)),
       ((ceilSite site).remainder, .pred (decide (len ≠ len / 128 * 128)))]
      ((ceilSite site).pc + 10) [((ceilSite site).count, b32 ((len + 127) / 128))] := by
    by_cases h : len = len / 128 * 128
    · have hPad : decide (len ≠ len / 128 * 128) = false := decide_eq_false (fun hn => hn h)
      fin_cases site <;> intro t ht <;> simp only [hPad] at ht <;> seg_fp ht using norm_bits
    · fin_cases site <;> intro t ht <;>
        simp only [decide_eq_true h] at ht <;> seg_fp ht using norm_bits
  exact hFirst.comp hLast

private theorem tripCausalWords (l : Launch) (g : Nat) {key query tile : Nat}
    (hQuery : query ≤ key) (hKey : key < 2 ^ 31)
    (hEnd : key - query + 256 * (tile + 1) < 2 ^ 31) :
    Seg kernel [] l g 3 449
      [(1801, b32 (256 * tile)), (1086, b32 key), (1085, b32 (2 ^ 32 - query))] 452
      [(1820, b32 (key - query + 256 * tile)),
       (1821, b32 (key - query + 256 * (tile + 1)))] := by
  intro t ht
  seg_fp ht using norm_bits

private theorem tripMin (l : Launch) (g : Nat) {a b : Nat}
    (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    Seg kernel [] l g 1 462 [(1818, b32 a), (1828, b32 b)] 463 [(1088, b32 (min a b))] := by
  have h32a : a < 2 ^ 32 := by omega
  have h32b : b < 2 ^ 32 := by omega
  have hMin : (IntOp.min false == IntOp.max false) = false := rfl
  by_cases h : a < b
  · intro t ht
    seg_fp ht using
      simp only [hMin, b32, truncBits_ofNat h32a (by decide), truncBits_ofNat h32b (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed ha, int32Signed hb,
        Int.ofNat_lt, h, decide_true, ↓reduceIte, min_eq_left h.le]
  · have hle : b ≤ a := by omega
    intro t ht
    seg_fp ht using
      simp only [hMin, b32, truncBits_ofNat h32a (by decide), truncBits_ofNat h32b (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed ha, int32Signed hb,
        Int.ofNat_lt, h, decide_false, ↓reduceIte, min_eq_right hle]

/-- The loader's upper visible K/V count agrees with MMA, and its lower-stage ceiling is
the same computation with the shorter causal extent. -/
theorem loaderVisibleTripsCore {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch tile : Nat} (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    {t : TState} (ht : At t 439
      [(1801, b32 (256 * tile)), (1086, b32 (p.kLength batch)),
       (1085, b32 (2 ^ 32 - p.qLength batch))]) :
    ∃ u, run kernel [] l g 35 t = some u ∧
      At u 474 [(1088, b32 (Mma.trips p batch tile)),
        (1818, b32 ((p.kLength batch + 127) / 128)),
        (1836, b32 ((p.kLength batch - p.qLength batch + 256 * tile + 128 + 127) / 128))] := by
  let key := p.kLength batch
  let query := p.qLength batch
  let first := key - query + 256 * tile
  let upper := first + 256
  let lower := first + 128
  let keyBlocks := (key + 127) / 128
  let upperBlocks := (upper + 127) / 128
  have hShape := hp.lengths batch hb
  have hKey : key < 2 ^ 31 := by dsimp [key]; omega
  have hUpper : upper < 2 ^ 31 := by
    dsimp [upper, first, key, query]
    omega
  have hLower : lower < 2 ^ 31 := by dsimp [upper, lower] at *; omega
  have hUpper' : key - query + 256 * (tile + 1) = upper := by dsimp [upper, first]; omega
  obtain ⟨v, hv, hV⟩ := blockCount 0 l g hKey t
    (ht.mono ⟨ht.2.2.2.2.2.1, trivial⟩)
  obtain ⟨_, hvFrame⟩ := loaderLinear (regs := [1801, 1086, 1085]) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  have hVMore := holdsSchedulerFrame ht.2.2.2.2 hvFrame (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨w, hw, hW⟩ := tripCausalWords l g hShape.2.1 hKey (hUpper'.symm ▸ hUpper) v
    (hV.mono hVMore)
  obtain ⟨_, hwFrame⟩ := loaderLinear (regs := [1818]) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  have hFirst : w.regs 1820 = some (b32 first) := hW.2.2.2.2.1
  have hKeyBlocks : w.regs 1818 = some (b32 keyBlocks) :=
    (hwFrame 1818 (by simp)).trans hV.2.2.2.2.1
  have hCaus : w.regs 1821 = some (b32 upper) := by
    rw [← hUpper']
    exact hW.2.2.2.2.2.1
  obtain ⟨x, hx, hX⟩ := blockCount 1 l g hUpper w (hW.mono ⟨hCaus, trivial⟩)
  obtain ⟨_, hxFrame⟩ := loaderLinear (regs := [1820, 1818]) (by decide) (by decide) hW.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hx
  have hA : keyBlocks < 2 ^ 31 := by dsimp [keyBlocks]; omega
  have hB : upperBlocks < 2 ^ 31 := by dsimp [upperBlocks]; omega
  obtain ⟨y, hy, hY⟩ := tripMin l g hA hB x
    (hX.mono ⟨(hxFrame 1818 (by simp)).trans hKeyBlocks, hX.2.2.2.2.1, trivial⟩)
  obtain ⟨_, hyFrame⟩ := loaderLinear (regs := [1820, 1818]) (by decide) (by decide) hX.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hy
  have hLow : Seg kernel [] l g 1 463 [(1820, b32 first)] 464 [(1829, b32 lower)] := by
    intro z hz
    seg_fp hz using norm_bits [lower]
  obtain ⟨z, hz, hZ⟩ := hLow y
    (hY.mono ⟨(hyFrame 1820 (by simp)).trans ((hxFrame 1820 (by simp)).trans hFirst), trivial⟩)
  obtain ⟨_, hzFrame⟩ := loaderLinear (regs := [1088, 1818]) (by decide) (by decide) hY.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hz
  obtain ⟨u, hu, hU⟩ := blockCount 2 l g hLower z hZ
  obtain ⟨_, huFrame⟩ := loaderLinear (regs := [1088, 1818]) (by decide) (by decide) hZ.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  refine ⟨u, run_comp (run_comp (run_comp (run_comp (run_comp hv hw) hx) hy) hz) hu, ?_⟩
  apply hU.mono
  have he : Mma.trips p batch tile = min keyBlocks upperBlocks := by
    change min keyBlocks ((key - query + 256 * (tile + 1) + 127) / 128) = _
    rw [hUpper']
  refine ⟨?_, ?_, hU.2.2.2.2.1, trivial⟩
  · rw [he]
    exact (huFrame 1088 (by simp)).trans ((hzFrame 1088 (by simp)).trans hY.2.2.2.2.1)
  · exact (huFrame 1818 (by simp)).trans ((hzFrame 1818 (by simp)).trans
      ((hyFrame 1818 (by simp)).trans ((hxFrame 1818 (by simp)).trans hKeyBlocks)))

end
end PTX.Kernels.TmlFa4Fwd.Loader

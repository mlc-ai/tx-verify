-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleCounter
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part124

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private theorem int32Signed {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

private theorem lowSevenMask {x : Nat} (hx : x < 2 ^ 32) :
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

private def ceilSite : Fin 2 → CeilSite
  | 0 => ⟨7960, 5959, 5963, 726, 5966⟩
  | 1 => ⟨7974, 5970, 5974, 729, 5977⟩

private theorem blockCount (site : Fin 2) (l : Launch) (g : Nat) {len : Nat}
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

private theorem causalLength (l : Launch) (g : Nat) {k q tile : Nat}
    (hk : k < 2 ^ 31) (hq : q ≤ k) (_hSum : k - q + 256 * (tile + 1) < 2 ^ 31) :
    Seg kernel [] l g 4 7970 [(5959, b32 k), (7276, b32 tile), (1635, b32 q)]
      7974 [(5970, b32 (k - q + 256 * (tile + 1))), (5967, b32 (256 * tile))] := by
  intro t ht
  seg_fp ht using norm_bits

/-- The correction loop count is the smaller of the two decoded block counts. -/
private theorem minBlockCount (l : Launch) (g : Nat) {keys causal : Nat}
    (hk : keys < 2 ^ 31) (hc : causal < 2 ^ 31) :
    Seg kernel [] l g 1 7984 [(5966, b32 keys), (5977, b32 causal)]
      7985 [(1636, b32 (min keys causal))] := by
  have h32k : keys < 2 ^ 32 := by omega
  have h32c : causal < 2 ^ 32 := by omega
  have hMin : (IntOp.min false == IntOp.max false) = false := rfl
  by_cases h : keys < causal
  · intro t ht
    seg_fp ht using
      (simp only [hMin, b32, truncBits_ofNat h32k (by decide), truncBits_ofNat h32c (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed hk, int32Signed hc,
        Int.ofNat_lt, h, decide_true, ↓reduceIte,
        min_eq_left h.le])
  · have hle : causal ≤ keys := by omega
    intro t ht
    seg_fp ht using
      (simp only [hMin, b32, truncBits_ofNat h32k (by decide), truncBits_ofNat h32c (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed hk, int32Signed hc,
        Int.ofNat_lt, h, decide_false, ↓reduceIte,
        min_eq_right hle])

set_option maxRecDepth 100000 in
private theorem tripCoreCode :
    ((kernel.code.drop 7960).take 25).all (fun i => Assumptions.coreOp i.op) = true := by
  kernel_rfl

private theorem tripCoreOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 7960 ≤ t.pc) (hHi : t.pc < 7985) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 7960).take 25 := by
      apply List.mem_of_getElem? (i := t.pc - 7960)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp tripCoreCode _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

/-- Correction and MMA use the same number of visible KV blocks for the selected tile.
The result is the word read by the correction lane's loop-entry predicate. -/
theorem correctionTripAndRowWithFrame {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch tile : Nat} (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch)
    {F : List (Nat × Value)}
    (hWrite : ((kernel.code.drop 7960).take 25).all
      (fun i => F.all (fun rv => !(writesRegs i.op).contains rv.1)) = true) :
    Seg kernel Assumptions.all l g 25 7960
      ([(5959, b32 (p.kLength batch)), (7276, b32 tile), (1635, b32 (p.qLength batch))] ++ F)
      7985 ((1636, b32 (Mma.trips p batch tile)) :: (5967, b32 (256 * tile)) :: F) := by
  let key := p.kLength batch
  let cause := key - p.qLength batch + 256 * (tile + 1)
  have hKeys := (hp.lengths batch hb).2.2
  have hFits := (Mma.trips_bounds hp hb htile).2.2
  have hLen := (hp.lengths batch hb).2.1
  have hk : key < 2 ^ 31 := by dsimp only [key]; omega
  have hCause : cause < 2 ^ 31 := hFits
  have ha : (key + 127) / 128 < 2 ^ 31 := by omega
  have hc : (cause + 127) / 128 < 2 ^ 31 := by omega
  intro t ht
  obtain ⟨s, hs, hS⟩ := blockCount 0 l g hk t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  have hFrame1 {r : Nat} (hr : r ∈ [5959, 7276, 1635]) : s.regs r = t.regs r :=
    schedulerLocalFrame (lo := 7960) (len := 10) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hs ht.1.ge (by rw [ht.1]) hr
  have hStart : At s 7970 [(5959, b32 key), (7276, b32 tile), (1635, b32 (p.qLength batch))] :=
    hS.mono ⟨(hFrame1 (by simp)).trans ht.2.2.2.2.1,
      (hFrame1 (by simp)).trans ht.2.2.2.2.2.1,
      (hFrame1 (by simp)).trans ht.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := causalLength l g hk hLen hFits s hStart
  obtain ⟨v, hv, hV⟩ := blockCount 1 l g hCause u
    (hU.mono ⟨hU.2.2.2.2.1, trivial⟩)
  have hSum := run_comp hu hv
  have hFrame2 : v.regs 5966 = s.regs 5966 :=
    schedulerLocalFrame (lo := 7970) (len := 14) (regs := [5966]) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hSum hStart.1.ge (by rw [hStart.1]) (by simp)
  obtain ⟨w, hw, hW⟩ := minBlockCount l g ha hc v
    (hV.mono ⟨hFrame2.trans hS.2.2.2.2.1, hV.2.2.2.2.1, trivial⟩)
  have hCore := run_comp (run_comp hs hSum) hw
  have hStraight : ((kernel.code.drop 7960).take (25 - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAll := schedulerLocalTransport (lo := 7960) (len := 25) hStraight
    (fun h0 h1 => tripCoreOut h0 h1) hCore ht.1.ge (by rw [ht.1])
  have hWrites : ((kernel.code.drop 7960).take 25).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    simpa only [List.all_map, Function.comp_def] using hWrite
  have hFrame : ∀ r ∈ F.map Prod.fst, w.regs r = t.regs r :=
    fun _ hm => schedulerLocalFrame (lo := 7960) (len := 25)
      hWrites hStraight hCore ht.1.ge (by rw [ht.1]) hm
  have hCarry := ((holds_append _ _ _).1 ht.2.2.2.2).2
  have hF := holdsSchedulerFrame hCarry hFrame (fun _ hm => List.mem_map_of_mem hm)
  have hRow : w.regs 5967 = some (b32 (256 * tile)) := by
    have hWrt : ((kernel.code.drop 7974).take 11).all
        (fun i => [5967].all (fun r => !(writesRegs i.op).contains r)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hKeep := schedulerLocalFrame (lo := 7974) (len := 11) hWrt
      (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hv hw)
      hU.1.ge (by rw [hU.1]) (show (5967 : Nat) ∈ [5967] by simp)
    exact hKeep.trans hU.2.2.2.2.2.1
  exact ⟨w, hAll, hW.mono ⟨hW.2.2.2.2.1, hRow, hF⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction

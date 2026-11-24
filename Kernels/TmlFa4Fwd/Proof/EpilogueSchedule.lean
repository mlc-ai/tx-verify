-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem int32Signed {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

theorem firstTileGate (l : Launch) (g : Nat) {lane batch begin finish : Nat}
    (hl : lane < 32) (hb : batch < 2 ^ 31) (hb32 : begin < 2 ^ 32) (he32 : finish < 2 ^ 32) :
    Seg kernel [] l g 6 2778
      [(1201, b32 lane), (7228, b32 batch), (7217, b32 begin), (2308, b32 finish)] 2784
      [(1202, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
       (7220, b32 0),
       (268, .pred (!decide (laneHasRequest lane batch)))] := by
  intro t ht
  have hL32 : lane < 2 ^ 32 := by omega
  have hL31 : lane < 2 ^ 31 := by omega
  have hL64 : lane < 2 ^ 64 := by omega
  have hB32 : batch < 2 ^ 32 := by omega
  have hNe : (lane : Int) ≠ 31 ↔ lane < 31 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hb32 (by decide), truncBits_ofNat he32 (by decide)]
    | (simp only [compare, Option.getD_some, truncBits_ofNat hL32 (by decide),
        truncBits_ofNat hB32 (by decide), int32Signed hL31, int32Signed hb,
        toNat_ofNat_lt hL64, Int.ofNat_lt, Bool.and_comm]
       have heq : (↑(truncBits 32 (BitVec.ofInt 64 31)).toNat : Int) = 31 := rfl
       simp only [heq, hNe]
       by_cases hcut : lane < batch <;> by_cases hlast : lane < 31 <;>
         simp [laneHasRequest, hcut, hlast])

/-- The four copies of the lane tile count in the entry and exit scans. -/
def ceilSite : Fin 4 → CeilSite
  | 0 => ⟨2785, 1202, 2312, 271, 7220⟩
  | 1 => ⟨2843, 1206, 2333, 285, 7220⟩
  | 2 => ⟨2994, 1209, 2405, 310, 7232⟩
  | 3 => ⟨3051, 1213, 2426, 324, 7232⟩

/-- Each active scan path rounds the query length up to a count of 256-row tiles. -/
theorem laneTileCount (site : Fin 4) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 (ceilSite site).pc [((ceilSite site).lengthReg, b32 len)]
      ((ceilSite site).pc + 10) [((ceilSite site).countReg, b32 ((len + 255) / 256))] := by
  have h32 : len < 2 ^ 32 := by omega
  have h31 : len < 2 ^ 31 := by omega
  have h64 : len < 2 ^ 64 := by omega
  have hx64 : len < 18446744073709551616 := h64
  have hDiv : len / 256 < 2 ^ 32 := by omega
  have hMask : len / 256 * 256 < 2 ^ 32 := by omega
  have shr31 : (len : Int) / 2 ^ 31 = 0 := by omega
  have shr8 : (len : Int) / 2 ^ 8 = (len / 256 : Nat) := by omega
  have s31 : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := rfl
  have s8 : min (truncBits 32 (BitVec.ofInt 64 8)).toNat 32 = 8 := rfl
  have s24 : (truncBits 32 (BitVec.ofInt 64 24)).toNat = 24 := rfl
  have z : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have z32 : truncBits 32 0 = 0 := rfl
  have zShift : (0 : BitVec 64) >>> 24 = 0 := rfl
  have h24 : ¬24 ≥ 32 := by decide
  have hNeg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hPos : (-1 : Int) < len := by omega
  have m32 : truncBits 32 (BitVec.ofInt 64 (-256)) = BitVec.ofNat 64 4294967040 := rfl
  have aZero : BitVec.ofNat 64 len + 0 = BitVec.ofNat 64 len := BitVec.add_zero _
  have hFirst : Seg kernel [] l g 8 (ceilSite site).pc [((ceilSite site).lengthReg, b32 len)]
      ((ceilSite site).pc + 8)
      [((ceilSite site).quotientReg, b32 (len / 256)),
       ((ceilSite site).remainderPred, .pred (decide (len ≠ len / 256 * 256)))] := by
    fin_cases site <;> intro t ht <;> seg_fp ht using
      simp only [b32, s31, s8, s24, ite_eq_right h24, shr31, shr8, z, z32, zShift,
        aZero, truncBits_ofNat h32 (by decide), m32,
        truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
        Option.getD_some, int32Signed h31, hNeg, gt_iff_lt, hPos, decide_true, Bool.true_and,
        toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
      all_goals
        simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, lowByteMask h32,
          truncBits_ofNat hMask (by decide),
          toNat_ofNat_lt (show len / 256 * 256 < 2 ^ 64 by omega)]
  have hLast : Seg kernel [] l g 2 ((ceilSite site).pc + 8)
      [((ceilSite site).quotientReg, b32 (len / 256)),
       ((ceilSite site).remainderPred, .pred (decide (len ≠ len / 256 * 256)))]
      ((ceilSite site).pc + 10) [((ceilSite site).countReg, b32 ((len + 255) / 256))] := by
    by_cases h : len = len / 256 * 256
    · have hPad : decide (len ≠ len / 256 * 256) = false := decide_eq_false (fun hn => hn h)
      fin_cases site <;> intro t ht <;> simp only [hPad] at ht <;> seg_fp ht using norm_bits
    · fin_cases site <;> intro t ht <;>
        simp only [decide_eq_true h] at ht <;> seg_fp ht using norm_bits
  exact hFirst.comp hLast

theorem firstLaneTileCount (l : Launch) (g : Nat) {len : Nat} (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 2785 [(1202, b32 len)] 2795 [(7220, b32 ((len + 255) / 256))] :=
  laneTileCount 0 l g hlen

/-- The first scheduler pass contributes a tile count only for request lanes. The sentinel
and lanes past the batch contribute zero even when the endpoint subtraction wraps. -/
theorem firstLaneTiles (l : Launch) (g : Nat) {lane batch begin finish : Nat}
    (hl : lane < 32) (hb : batch < 2 ^ 31) (hb32 : begin < 2 ^ 32) (he32 : finish < 2 ^ 32)
    (hmono : laneHasRequest lane batch → begin ≤ finish) (hlen : finish - begin < 2 ^ 30) :
    Seg kernel [] l g (if laneHasRequest lane batch then 17 else 7) 2778
      [(1201, b32 lane), (7228, b32 batch), (7217, b32 begin), (2308, b32 finish)] 2795
      [(7220, b32 (if laneHasRequest lane batch then (finish - begin + 255) / 256 else 0))] := by
  intro t ht
  obtain ⟨u, hRun, hu⟩ := firstTileGate l g hl hb hb32 he32 t ht
  have hpred : u.regs 268 = some (.pred (!decide (laneHasRequest lane batch))) :=
    holds_mem hu.2.2.2.2 (by simp)
  obtain ⟨v, hBra, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2784 _ hu hpred (by simp)
  by_cases h : laneHasRequest lane batch
  · have hPc : v.pc = 2785 := by simpa [h] using hv.1
    have hValue : truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin) =
        BitVec.ofNat 64 (finish - begin) := by
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) (hmono h),
        truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
    have hV : At v 2785 [(1202, b32 (finish - begin))] := by
      refine ⟨hPc, hv.2.1, hv.2.2.1, hv.2.2.2.1, ?_⟩
      have hReg := holds_mem hv.2.2.2.2 (by simp :
        (1202, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))) ∈ _)
      simp [Holds, b32, hValue] at hReg ⊢
      exact hReg
    obtain ⟨w, hRound, hw⟩ := firstLaneTileCount l g hlen v hV
    rw [ite_eq_left h, ite_eq_left h]
    exact ⟨w, run_comp (run_comp hRun hBra) hRound, hw⟩
  · have hPc : v.pc = 2795 := by simpa [h] using hv.1
    have hR : v.regs 7220 = some (b32 0) := holds_mem hv.2.2.2.2 (by simp)
    refine ⟨v, by simpa [h] using run_comp hRun hBra, hPc, hv.2.1, hv.2.2.1,
      hv.2.2.2.1, ?_⟩
    simp [h, Holds, hR]

def firstScanPc (stage : Fin 5) : Nat := 2796 + 4 * stage.val

set_option maxRecDepth 2000 in
theorem firstScanHeadCount {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (count : Nat) :
    Seg kernel [] l g 1 2795 [(7220, b32 count)] 2796
      [(7220, b32 count), (7138, b32 p.heads)] := by
  intro t ht
  let u := next (setReg t 7138 (b32 p.heads))
  obtain ⟨hBound, hParam⟩ := hp.values (17, p.heads) (by simp [Params.scalarWords])
  have hRead : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_2795 rfl ht
    rw [execLocalA_nil, execLocal_mem rfl]
    have hName : kernel.name =
        "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at_\
        _tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o\
        1i64div8_0" := rfl
    have h17 : toString (17 : Nat) = "17" := by
      rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
      simp only [show (17 / 10 : Nat) = 1 by decide, show (17 % 10 : Nat) = 7 by decide,
        Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 7) (by decide),
        Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_seven.mpr rfl]
      rfl
    have hParamName : param 17 =
        "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_obje\
        ct_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf\
        16gmemalign16o1i64div8_0_param_17" := by
      unfold param
      rw [hName, h17]
      rfl
    change l.params (param 17) = some (BitVec.ofNat 64 p.heads) at hParam
    rw [hParamName] at hParam
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      hParam, DType.width, MemExt.extendBits_same, pure, Except.pure,
      truncBits_ofNat hBound (by decide)]
    rfl
  have hCount : t.regs 7220 = some (b32 count) := holds_mem ht.2.2.2.2 (by simp)
  have hPc : u.pc = 2796 := by change t.pc + 1 = 2796; rw [ht.1]
  refine ⟨u, hRead, hPc, ht.2.1, ht.2.2.1, ht.2.2.2.1, ?_⟩
  simp [Holds, u, next, setReg, hCount]

def firstScanSrc : Fin 5 → Nat
  | 0 => 7220
  | 1 => 2317
  | 2 => 2320
  | 3 => 2323
  | 4 => 2326

def firstScanDst (stage : Fin 5) : Nat := 2315 + 3 * stage.val

def firstScanResult (stage : Fin 5) : Nat :=
  if stage.val = 4 then 7221 else 2317 + 3 * stage.val

theorem firstScanCode (stage : Fin 5) :
    kernel.code[firstScanPc stage]? = some ⟨none, .warp
      { kind := .shfl .up
        ty := some (.int .b 32)
        dsts := [some (firstScanDst stage)]
        srcs := [.reg (firstScanSrc stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0]
        mask := some (.imm (-1)) }⟩ := by
  fin_cases stage
  · exact Flow.code_2796
  · exact Flow.code_2800
  · exact Flow.code_2804
  · exact Flow.code_2808
  · exact Flow.code_2812

/-- Each of the first pass's five scan rounds shuffles the previous partial sum by the exact
doubling offset. -/
theorem firstScanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (stage : Fin 5) (sum : Nat)
    (hpc : t.pc = firstScanPc stage) (hf : t.fault = none)
    (hv : t.regs (firstScanSrc stage) = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (firstScanDst stage) value))) := by
  have hb : l.block % 32 = 0 := by rw [hp.block]
  have hc := firstScanCode stage
  rw [← hpc] at hc
  rw [out_event hf hc rfl rfl]
  change Out.ev (shflTmpl l g t .up (firstScanDst stage) none (.reg (firstScanSrc stage))
    (.imm ((2 ^ stage.val : Nat) : Int)) (.imm 0) (.imm (-1))) = _
  have hWidth : 2 ^ stage.val < 2 ^ 32 := by
    have hs := stage.isLt
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hBits : readBits l g t 32 (.imm ((2 ^ stage.val : Nat) : Int)) =
      .ok (BitVec.ofNat 64 (2 ^ stage.val)) := by
    simp only [readBits, BitVec.ofInt_natCast, truncBits_ofNat hWidth (by decide),
      pure, Except.pure]
  have hm : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hz : readBits l g t 32 (.imm 0) = .ok 0 := rfl
  simp only [shflTmpl, readValue, readReg, hv, hb, hBits, hm, hz, pure, Except.pure,
    toNat_ofNat_lt (show 2 ^ stage.val < 2 ^ 64 by omega)]
  rfl

private def firstScanGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2 ^ stage.val ≤ lane)

private theorem firstScanCompare (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) :
    Seg kernel [] l g 1 (firstScanPc stage + 1)
      [(1201, b32 lane), (firstScanSrc stage, b32 left), (firstScanDst stage, b32 recv)]
      (firstScanPc stage + 2)
      [(272 + stage.val, .pred (firstScanGuard stage lane)),
       (firstScanSrc stage, b32 left), (firstScanDst stage, b32 recv)] := by
  have hLane : lane < 2 ^ 32 := by omega
  have hLane64 : lane < 2 ^ 64 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  fin_cases stage <;>
    intro t ht <;>
    seg_fp ht using
      simp only [firstScanGuard, Nat.reduceEqDiff, ↓reduceIte, compare, Option.getD_some,
        truncBits_ofNat hLane (by decide), toNat_ofNat_lt hLane64,
        Value.pred.injEq, decide_eq_decide, hz, h1, h3, h7, h15]
      all_goals omega

private theorem firstScanSelect (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (firstScanPc stage + 2)
      [(272 + stage.val, .pred (firstScanGuard stage lane)),
       (firstScanSrc stage, b32 left), (firstScanDst stage, b32 recv)]
      (firstScanPc stage + 4)
      [(firstScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  have hLeft : left < 2 ^ 32 := by omega
  have hRecv : recv < 2 ^ 32 := by omega
  by_cases h : 2 ^ stage.val ≤ lane
  · have hp : firstScanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [firstScanGuard, hst, show lane ≠ 0 by omega]
      · simp [firstScanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_left h]
  · have hp : firstScanGuard stage lane = decide (stage.val = 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [firstScanGuard, hst, show lane = 0 by omega]
      · simp [firstScanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_right h]

/-- The three local instructions after an up-shuffle implement its guarded addition. -/
theorem firstScanCombine (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 3 (firstScanPc stage + 1)
      [(1201, b32 lane), (firstScanSrc stage, b32 left), (firstScanDst stage, b32 recv)]
      (firstScanPc stage + 4)
      [(firstScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] :=
  (firstScanCompare stage l g hl).comp (firstScanSelect stage l g hl hsum)

/-- The shuffle source given by PTX and the decoded local addition implement one round of the
inclusive prefix scan. -/
theorem firstScanFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hl : lane < 32)
    (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 3 (firstScanPc stage + 1)
      [(1201, b32 lane), (firstScanSrc stage, b32 (prefixWindow xs (2 ^ stage.val) lane)),
       (firstScanDst stage,
         b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (firstScanPc stage + 4)
      [(firstScanResult stage, b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := firstScanCombine stage l g hl hsum
  rw [firstScanSource] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

theorem firstGroupTotalTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (sum : Nat)
    (hpc : t.pc = 2816) (hf : t.fault = none) (hv : t.regs 7221 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7222 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2816) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7222 none (.reg 7221) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

/-- The first group's tile total is multiplied by the number of heads before comparing it to
the CTA index. -/
theorem firstGroupLimit (l : Launch) (g : Nat) {count heads cta : Nat}
    (hc : count < 2 ^ 31) (hh : heads < 2 ^ 31) (hg : cta < 2 ^ 31)
    (htotal : count * heads < 2 ^ 31) :
    Seg kernel [] l g 3 2817 [(7222, b32 count), (7138, b32 heads), (1072, b32 cta)] 2820
      [(7224, b32 (count * heads)), (277, .pred (decide (cta < count * heads))),
       (7223, b32 0)] := by
  intro t ht
  have hCount : count < 2 ^ 32 := by omega
  have hHeads : heads < 2 ^ 32 := by omega
  have hCta : cta < 2 ^ 32 := by omega
  have hTotal : count * heads < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_mul, truncBits_ofNat hCount (by decide),
        truncBits_ofNat hHeads (by decide), truncBits_ofNat hCta (by decide),
        truncBits_ofNat hTotal (by decide), compare, Option.getD_some, int32Signed hg,
        int32Signed htotal, Int.ofNat_lt]

/-- The decoded branch bounds the group search against the runtime batch count. -/
theorem groupAvailability (l : Launch) (g : Nat) {first batch : Nat}
    (hFirst : first < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 5 2878 [(7223, b32 first), (7228, b32 batch)]
      (if batch ≤ first then 2947 else 2883) [(782, .pred false)] := by
  intro t ht
  have hF32 : first < 2 ^ 32 := by omega
  have hB32 : batch < 2 ^ 32 := by omega
  obtain ⟨u, hPrep, hu⟩ : ∃ u, run kernel [] l g 4 t = some u ∧
      At u 2882 [(292, .pred (decide (batch ≤ first))), (782, .pred false)] := by
    seg_fp ht using
      first
      | rfl
      | simp only [compare, Option.getD_some, truncBits_ofNat hF32 (by decide),
          truncBits_ofNat hB32 (by decide), int32Signed hFirst, int32Signed hBatch,
          ge_iff_le, Int.ofNat_le]
  obtain ⟨v, hBra, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2882 (decide (batch ≤ first)) hu hu.2.2.2.2.1 (by simp)
  refine ⟨v, run_comp hPrep hBra, ?_⟩
  simpa only [decide_eq_true_eq] using hv.mono hv.2.2.2.2.2

/-- If no batch remains after the scan, the early exit leaves the tile selection false. -/
theorem exhaustedGroup (l : Launch) (g : Nat) {first batch : Nat}
    (hFirst : first < 2 ^ 31) (hBatch : batch < 2 ^ 31) (hExhausted : batch ≤ first) :
    Seg kernel [] l g 5 2878 [(7223, b32 first), (7228, b32 batch)] 2947
      [(782, .pred false)] := by
  simpa only [ite_eq_left hExhausted] using groupAvailability l g hFirst hBatch

/-- Encode the selected tile as two to the thirtieth plus 256 times the tile. -/
theorem selectedTileRegisters (l : Launch) (g : Nat) {batch batches head tile : Nat}
    (hb : batch < batches) (hBatch : batches < 2 ^ 31) (htile : 256 * tile < 2 ^ 30) :
    Seg kernel [] l g 3 2944
      [(7228, b32 batch), (7146, b32 batches), (7227, b32 head), (2388, b32 tile)] 2947
      [(782, .pred true), (7228, b32 batch), (7227, b32 head),
       (7226, b32 (2 ^ 30 + 256 * tile))] := by
  intro t ht
  have hB32 : batches < 2 ^ 32 := by omega
  have hb32 : batch < 2 ^ 32 := by omega
  have hb31 : batch < 2 ^ 31 := by omega
  seg_fp ht using
    first
    | simp only [compare, Option.getD_some, truncBits_ofNat hb32 (by decide),
        truncBits_ofNat hB32 (by decide), int32Signed hb31, int32Signed hBatch, Int.ofNat_lt,
        hb, decide_true]
    | norm_bits

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

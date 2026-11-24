-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueSchedule
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The fallback iterates over groups of 31 requests. Its first iteration remembers the first
group's CTA limit and prepares a sentinel beyond the CTA asking for work. -/
theorem enterGroupSearch (l : Launch) (g : Nat) {cta limit : Nat} (hCta : cta + 1 < 2 ^ 32) :
    Seg kernel [] l g 3 2821 [(1072, b32 cta), (7224, b32 limit)] 2824
      [(1203, b32 (cta + 1)), (7223, b32 0), (7218, b32 limit)] := by
  intro t ht
  seg_fp ht using first | rfl | norm_bits

/-- Advance to the next group, saturating its base at the batch sentinel. -/
theorem advanceGroup (l : Launch) (g : Nat) {first batch stop : Nat}
    (hNext : first + 31 < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 4 2824 [(7223, b32 first), (7228, b32 batch), (1203, b32 stop)] 2828
      [(1204, b32 (first + 31)), (278, .pred (decide (batch ≤ first + 31))),
       (7223, b32 (min (first + 31) batch)), (7224, b32 stop)] := by
  intro t ht
  have hFirst32 : first < 2 ^ 32 := by omega
  have hNext32 : first + 31 < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  have hLit : truncBits 32 (BitVec.ofInt 64 31) = BitVec.ofNat 64 31 := rfl
  seg_fp ht using
    simp only [b32, hLit, ← BitVec.ofNat_add, truncBits_ofNat hFirst32 (by decide),
      truncBits_ofNat hNext32 (by decide), truncBits_ofNat hBatch32 (by decide), compare,
      Option.getD_some, signedWord hNext, signedWord hBatch, Int.ofNat_le, ge_iff_le]
    all_goals
      by_cases h : first + 31 < batch
      · simp [Nat.min_eq_left (Nat.le_of_lt h)]
        omega
      · simp [Nat.min_eq_right (Nat.le_of_not_lt h)]
        omega

variable {p : Params} {l : Launch} {m : Mem0}

theorem advanceGroup_of_pre (hp : Pre p l m) (g : Nat) {first stop : Nat} (hf : first < p.batch) :
    let nextGroup := min (first + 31) p.batch
    first < nextGroup ∧ nextGroup ≤ p.batch ∧
      Seg kernel [] l g 4 2824
        [(7223, b32 first), (7228, b32 p.batch), (1203, b32 stop)] 2828
        [(1204, b32 (first + 31)), (278, .pred (decide (p.batch ≤ first + 31))),
         (7223, b32 nextGroup), (7224, b32 stop)] := by
  have hSize := hp.shape.2.2.2.2.2
  have hNext : first + 31 < 2 ^ 31 := by omega
  obtain ⟨hProgress, hLimit⟩ := groupSkip_progress hf
  exact ⟨by simpa only [Nat.min_comm] using hProgress,
    by simpa only [Nat.min_comm] using hLimit, advanceGroup l g hNext hp.shape.2.1⟩

/-- Lanes beyond the batch sentinel enter a shuffle with zero instead of reading cuQ. -/
theorem groupLaneGate (l : Launch) (g : Nat) {first lane batch : Nat}
    (hIndex : first + lane < 2 ^ 31) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 3 2829 [(1204, b32 first), (1201, b32 lane), (7228, b32 batch)] 2832
      [(1205, b32 (first + lane)), (279, .pred (decide (batch < first + lane))),
       (7219, b32 0)] := by
  intro t ht
  have hIdx32 : first + lane < 2 ^ 32 := by omega
  have hFirst32 : first < 2 ^ 32 := by omega
  have hLane32 : lane < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [b32, ← BitVec.ofNat_add, truncBits_ofNat hFirst32 (by decide),
        truncBits_ofNat hLane32 (by decide), truncBits_ofNat hIdx32 (by decide),
        truncBits_ofNat hBatch32 (by decide), compare, Option.getD_some,
        signedWord hIndex, signedWord hBatch, Int.ofNat_lt, gt_iff_lt]

private theorem cuQLaneBounds (hp : Pre p l m) {index : Nat} (hi : index ≤ p.batch) :
    index < 2 ^ 31 ∧ p.cuQBase + 4 * index < 2 ^ 64 := by
  have hB := hp.shape.2.1
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  omega

theorem groupLaneAddress (hp : Pre p l m) (g : Nat) {index : Nat} (hi : index ≤ p.batch) :
    Seg kernel [] l g 2 2833 [(1205, b32 index), (7506, b64 p.cuQBase)] 2835
      [(7865, b64 (p.cuQBase + 4 * index))] := by
  intro t ht
  obtain ⟨h31, hAddr⟩ := cuQLaneBounds hp hi
  have h32 : index < 2 ^ 32 := by omega
  have hOff : 4 * index < 2 ^ 64 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hI4 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hPr : (index : Int) * 4 = ((4 * index : Nat) : Int) := by push_cast; omega
  seg_fp ht using simp only [b64, kind_s_beq_s, ↓reduceIte, hI4, signedWord h31,
    truncBits_ofNat h32 (by decide), truncBits_ofNat hOff (by decide),
    truncBits_ofNat hBase (by decide), hPr, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    truncBits_ofNat hAddr (by decide)]

/-- Each participating lane reads its own offset in the current group. -/
theorem groupLaneRead (hp : Pre p l m) (g : Nat) (t : TState) {index : Nat} (hi : index ≤ p.batch)
    (ht : At t 2835 [(7865, b64 (p.cuQBase + 4 * index))]) :
    out kernel [] l g t = .ev (.read
      { loc := globalLoc (p.cuQBase + 4 * index), size := 4 } (afterLoad t [7219])) := by
  have hBase := (cuQLaneBounds hp hi).2
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  have ha : (p.cuQBase + 4 * index) % 4 = 0 := by omega
  have hr : t.regs 7865 = some (b64 (p.cuQBase + 4 * index)) := holds_mem ht.2.2.2.2 (by simp)
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_2835) rfl rfl]
  change Out.ev (loadTmpl [] l g t .global false 32 [7219] 7865 0) = _
  exact congrArg Out.ev (loadTmpl_global (w := 32) ht.2.1 hr hBase (by decide) ha)

theorem groupLastLaneCheck (l : Launch) (g : Nat) {lane : Nat} (hl : lane < 32) :
    Seg kernel [] l g 1 2836 [(1201, b32 lane)] 2837 [(280, .pred (decide (lane = 31)))] := by
  intro t ht
  have hLane32 : lane < 2 ^ 32 := by omega
  have hLane64 : lane < 2 ^ 64 := by omega
  have h31 : (↑(truncBits 32 (BitVec.ofInt 64 31)).toNat : Int) = 31 := rfl
  seg_fp ht using
    simp only [compare, Option.getD_some, truncBits_ofNat hLane32 (by decide),
      toNat_ofNat_lt hLane64, h31, Value.pred.injEq, decide_eq_decide]
    omega

theorem groupDownTemplate (hp : Pre p l m) (g : Nat) (t : TState) (cuq : Nat) (hpc : t.pc = 2837)
    (hf : t.fault = none) (hv : t.regs 7219 = some (b32 cuq)) :
    out kernel [] l g t = .ev (.shfl .down (b32 cuq) 1 31
      (fun value _ => next (setReg t 2329 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2837) rfl rfl]
  change Out.ev (shflTmpl l g t .down 2329 none (.reg 7219) (.imm 1) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

/-- Each eligible lane subtracts its two adjacent offsets. The sentinel and any lane outside
the batch skip rounding and pass a zero contribution to the scan. -/
theorem groupTileGate (l : Launch) (g : Nat) {lane index batch begin finish : Nat}
    (hl : lane < 32) (hi : index < 2 ^ 31) (hb : batch < 2 ^ 31)
    (hb32 : begin < 2 ^ 32) (he32 : finish < 2 ^ 32) :
    Seg kernel [] l g 4 2838
      [(7219, b32 begin), (2329, b32 finish), (1205, b32 index), (7228, b32 batch),
       (280, .pred (decide (lane = 31)))] 2842
      [(1206, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
       (7220, b32 0), (282, .pred (!decide (index < batch ∧ lane < 31)))] := by
  intro t ht
  have hi32 : index < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hb32 (by decide), truncBits_ofNat he32 (by decide)]
    | (simp only [compare, Option.getD_some, truncBits_ofNat hi32 (by decide),
        truncBits_ofNat hBatch32 (by decide), signedWord hi, signedWord hb, ge_iff_le,
        Int.ofNat_le, Value.pred.injEq]
       by_cases hLane : lane < 31 <;> by_cases hBatch : index < batch <;>
         simp [hLane, hBatch,
           show lane = 31 ↔ ¬lane < 31 by omega,
           show batch ≤ index ↔ ¬index < batch by omega])

theorem groupTileContribution (l : Launch) (g : Nat) (eligible : Bool) (len : Nat)
    (hlen : eligible = true → len < 2 ^ 30) :
    Seg kernel [] l g (if eligible then 11 else 1) 2842
      [(282, .pred (!eligible)), (1206, b32 len), (7220, b32 0)] 2853
      [(7220, b32 (if eligible then (len + 255) / 256 else 0))] := by
  intro t ht
  have hReg : t.regs 282 = some (.pred (!eligible)) := holds_mem ht.2.2.2.2 (by simp)
  obtain ⟨v, hRun, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2842 _ ht hReg (by simp)
  cases eligible
  · exact ⟨v, hRun, hv.mono hv.2.2.2.2.2.2⟩
  · have h : At v 2843 [(1206, b32 len)] := hv.mono ⟨hv.2.2.2.2.2.1, trivial⟩
    obtain ⟨w, hRound, hw⟩ := laneTileCount 1 l g (hlen rfl) v h
    exact ⟨w, run_comp hRun hRound, hw⟩

def groupScanPc (stage : Fin 5) : Nat := 2858 + 3 * stage.val

def groupScanSrc (stage : Fin 5) : Nat :=
  if stage.val = 0 then 7220 else 2335 + 3 * stage.val

def groupScanDst (stage : Fin 5) : Nat := 2336 + 3 * stage.val

def groupScanResult (stage : Fin 5) : Nat :=
  if stage.val = 4 then 7221 else 2338 + 3 * stage.val

def groupScanGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2 ^ stage.val ≤ lane)

/-- Prepare the five guards for the up-shuffles that follow a group reload. -/
theorem groupScanPredicates (l : Launch) (g : Nat) {lane count : Nat} (hl : lane < 32) :
    Seg kernel [] l g 5 2853 [(1201, b32 lane), (7220, b32 count)] 2858
      [(286, .pred (decide (16 ≤ lane))), (287, .pred (decide (8 ≤ lane))),
       (288, .pred (decide (4 ≤ lane))), (289, .pred (decide (2 ≤ lane))),
       (290, .pred (decide (lane = 0))), (7220, b32 count)] := by
  intro t ht
  have hLane32 : lane < 2 ^ 32 := by omega
  have hLane64 : lane < 2 ^ 64 := by omega
  have h0 : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  seg_fp ht using
    simp only [compare, Option.getD_some, truncBits_ofNat hLane32 (by decide),
      toNat_ofNat_lt hLane64, Value.pred.injEq, decide_eq_decide, h0, h1, h3, h7, h15]
    all_goals omega

theorem groupScanInstr (stage : Fin 5) :
    kernel.code[groupScanPc stage]? = some ⟨none, .warp
      { kind := .shfl .up
        ty := some (.int .b 32)
        dsts := [some (groupScanDst stage)]
        srcs := [.reg (groupScanSrc stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0]
        mask := some (.imm (-1)) }⟩ := by
  fin_cases stage
  · exact Flow.code_2858
  · exact Flow.code_2861
  · exact Flow.code_2864
  · exact Flow.code_2867
  · exact Flow.code_2870

theorem groupScanTemplate (hp : Pre p l m) (g : Nat) (t : TState) (stage : Fin 5) (sum : Nat)
    (hpc : t.pc = groupScanPc stage) (hf : t.fault = none)
    (hv : t.regs (groupScanSrc stage) = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (groupScanDst stage) value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [out_event hf (by rw [hpc]; exact groupScanInstr stage) rfl rfl]
  change Out.ev (shflTmpl l g t .up (groupScanDst stage) none (.reg (groupScanSrc stage))
    (.imm ((2 ^ stage.val : Nat) : Int)) (.imm 0) (.imm (-1))) = _
  have hWidth : 2 ^ stage.val < 2 ^ 32 :=
    Nat.pow_lt_pow_right (by decide) (lt_trans stage.isLt (by decide))
  have hBits : readBits l g t 32 (.imm ((2 ^ stage.val : Nat) : Int)) =
      .ok (BitVec.ofNat 64 (2 ^ stage.val)) := by
    simp only [readBits, BitVec.ofInt_natCast, truncBits_ofNat hWidth (by decide),
      pure, Except.pure]
  have hMask : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hZero : readBits l g t 32 (.imm 0) = .ok 0 := rfl
  simp only [shflTmpl, readValue, readReg, hv, hBlock, hBits, hMask, hZero, pure, Except.pure,
    toNat_ofNat_lt (show 2 ^ stage.val < 2 ^ 64 by omega)]
  rfl

theorem groupScanCombine (stage : Fin 5) (l : Launch) (g : Nat) {lane left recv : Nat}
    (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (groupScanPc stage + 1)
      [(290 - stage.val, .pred (groupScanGuard stage lane)),
       (groupScanSrc stage, b32 left), (groupScanDst stage, b32 recv)]
      (groupScanPc stage + 3)
      [(groupScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  by_cases h : 2 ^ stage.val ≤ lane
  · have hGuard : groupScanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hs : stage.val = 0
      · rw [hs, Nat.pow_zero] at h
        simp [groupScanGuard, hs, show lane ≠ 0 by omega]
      · simp [groupScanGuard, hs, h]
    fin_cases stage <;> intro t ht <;>
      simp only [hGuard] at ht <;> seg_fp ht using norm_bits [ite_eq_left h]
  · have hGuard : groupScanGuard stage lane = decide (stage.val = 0) := by
      by_cases hs : stage.val = 0
      · rw [hs, Nat.pow_zero] at h
        simp [groupScanGuard, hs, show lane = 0 by omega]
      · simp [groupScanGuard, hs, h]
    fin_cases stage <;> intro t ht <;>
      simp only [hGuard] at ht <;> seg_fp ht using norm_bits [ite_eq_right h]

theorem groupScanFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 2 (groupScanPc stage + 1)
      [(290 - stage.val, .pred (groupScanGuard stage lane)),
       (groupScanSrc stage, b32 (prefixWindow xs (2 ^ stage.val) lane)),
       (groupScanDst stage,
         b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (groupScanPc stage + 3)
      [(groupScanResult stage, b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := groupScanCombine stage l g (lane := lane) hsum
  rw [firstScanSource] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

theorem groupTotalTemplate (hp : Pre p l m) (g : Nat) (t : TState) (sum : Nat) (hpc : t.pc = 2873)
    (hf : t.fault = none) (hv : t.regs 7221 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7222 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_2873) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7222 none (.reg 7221) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hBlock, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

/-- Use lane 31's total for the current group and either move to the next group or select work
within this one. The cutoff remains a signed scheduler word by the launch precondition. -/
theorem groupLimit (hp : Pre p l m) (g : Nat) {first cta : Nat} (hf : first ≤ p.batch)
    (hCta : cta < 2 ^ 31) :
    let count := ∑ lane ∈ Finset.range 32, groupLaneTiles p first lane
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    Seg kernel [] l g 4 2874
      [(7222, b32 count), (7138, b32 p.heads),
       (7218, b32 (tilePrefix p first * p.heads)), (1072, b32 cta)]
      (if limit ≤ cta then 2824 else 2878) [(7218, b32 limit), (7224, b32 limit)] := by
  dsimp only
  let count := ∑ lane ∈ Finset.range 32, groupLaneTiles p first lane
  let start := tilePrefix p first * p.heads
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  have hFormula : count * p.heads + start = limit := by
    have hi := groupTiles_eq p hf (by decide : 32 ≤ 32)
    change tilePrefix p first + count = tilePrefix p (min p.batch (first + 31)) at hi
    simpa only [Nat.add_mul, Nat.add_comm, start, limit] using
      congrArg (fun n => n * p.heads) hi
  have hh := hp.heads_signed
  have hLimit : limit < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hStart : start < 2 ^ 31 := hp.prefixWork_signed hf
  have hHeads : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hCount : count < 2 ^ 32 := by
    have := Nat.le_mul_of_pos_right count hHeads
    omega
  have hh32 : p.heads < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hLimit32 : limit < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  intro t ht
  change At t 2874 [(7222, b32 count), (7138, b32 p.heads), (7218, b32 start), (1072, b32 cta)]
    at ht
  obtain ⟨u, hRun, hu⟩ : ∃ u, run kernel [] l g 3 t = some u ∧
      At u 2877 [(291, .pred (decide (limit ≤ cta))), (7218, b32 limit), (7224, b32 limit)] := by
    seg_fp ht using
      simp only [b32, truncBits_ofNat hCount (by decide), truncBits_ofNat hh32 (by decide),
        truncBits_ofNat hStart32 (by decide), truncBits_ofNat hCta32 (by decide),
        ← BitVec.ofNat_add, ← BitVec.ofNat_mul, hFormula, truncBits_ofNat hLimit32 (by decide),
        compare, Option.getD_some, signedWord hLimit, signedWord hCta, Int.ofNat_le]
  have hReg : u.regs 291 = some (.pred (decide (limit ≤ cta))) :=
    holds_mem hu.2.2.2.2 (by simp)
  obtain ⟨v, hBra, hv⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2877 _ hu hReg (by simp)
  refine ⟨v, run_comp hRun hBra, ?_⟩
  change At v (if limit ≤ cta then 2824 else 2878) [(7218, b32 limit), (7224, b32 limit)]
  simpa only [decide_eq_true_eq] using hv.mono hv.2.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

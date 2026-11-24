-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem toSignedWord {w : Nat} (hWord : w < 2 ^ 32) :
    toSigned 32 (BitVec.ofNat 64 w) = if w < 2 ^ 31 then (w : Int) else (w : Int) - 2 ^ 32 := by
  simp only [toSigned, toNat_ofNat_lt (show w < 2 ^ 64 by omega), Nat.mod_eq_of_lt hWord]

private def countdown (w : Nat) : Nat := (w + (2 ^ 32 - 1)) % 2 ^ 32

private theorem countdownPos {w : Nat} (hWord : w < 2 ^ 32) (hPos : 0 < w) :
    countdown w = w - 1 := by
  have hSum : w + (2 ^ 32 - 1) = 2 ^ 32 + (w - 1) := by omega
  rw [countdown, hSum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega)]

private theorem rawCountdown {l : Launch} {g w : Nat} (hWord : w < 2 ^ 32) :
    Seg kernel Assumptions.all l g 4 477 [(1088, b32 w)] 481
      [(1088, b32 w), (1091, b32 (countdown w))] := by
  have hd : countdown w < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hAdd : truncBits 32
        (BitVec.ofNat 64 w + truncBits 32 (BitVec.ofInt 64 (-1))) =
      BitVec.ofNat 64 (countdown w) := by
    have hMinusOne : truncBits 32 (BitVec.ofInt 64 (-1)) = BitVec.ofNat 64 (2 ^ 32 - 1) := rfl
    rw [hMinusOne, ← BitVec.ofNat_add, truncBits, toNat_ofNat_lt (by omega)]
    rfl
  have hSh : (truncBits 32 (BitVec.ofInt 64 7)).toNat = 7 := rfl
  have hZero : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  let pick := decide (0 < toSigned 32 (BitVec.ofNat 64 w))
  let row := truncBits 32 (BitVec.ofNat 64 (countdown w) <<< 7)
  have hSeg : Seg kernel [] l g 3 477 [(1088, b32 w)] 480
      [(121, .pred pick), (1092, .bits 32 row), (1091, b32 (countdown w))] := by
    intro t ht
    seg_fp ht using simp only [pick, row, b32, truncBits_ofNat hWord (by decide), hAdd,
      truncBits_ofNat hd (by decide), compare, Option.getD_some, hZero, gt_iff_lt, hSh,
      show ¬ 7 ≥ 32 by decide, ↓reduceIte]
  intro s hs
  obtain ⟨t, ht, hT⟩ := hSeg s hs
  have hFinish : ∃ u, run kernel [] l g 1 t = some u ∧
      At u 481 [(1091, b32 (countdown w))] := by
    let u := next (setReg t 1838 (if pick then .bits 32 row else b32 0))
    have hr : run kernel [] l g 1 t = some u := by
      apply run_local Flow.code_480 rfl hT
      rw [execLocalA_nil, execLocal_selp rfl]
      cases hp : pick <;>
        simp [execMove, readReg, readValue, hT.2.2.2.2.1, hT.2.2.2.2.2.1,
          DType.width, Value.bytes, b32, readBits, truncBits, bind, Except.bind,
          pure, Except.pure, u, hp]
    exact ⟨u, hr, by simp [u, At, next, setReg, hT.1, hT.2.1, hT.2.2.1,
      hT.2.2.2.1, hT.2.2.2.2.2.2.1]⟩
  obtain ⟨u, hu, hU⟩ := hFinish
  obtain ⟨hRun, hFrame⟩ := loaderLinear (regs := [1088]) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp ht hu)
  exact ⟨u, hRun, hU.mono ⟨(hFrame 1088 (by simp)).trans hs.2.2.2.2.1,
    hU.2.2.2.2.1, trivial⟩⟩

private theorem rawWarmSkip {l : Launch} {g w : Nat} (hWord : w < 2 ^ 32)
    (hSkip : toSigned 32 (BitVec.ofNat 64 w) < 2) :
    Seg kernel Assumptions.all l g 4 908 [(1088, b32 w)] 1353 [] := by
  have hTwo : toSigned 32 (truncBits 32 (BitVec.ofInt 64 2)) = 2 := rfl
  have hCalc : Seg kernel [] l g 3 908 [(1088, b32 w)] 911 [(166, .pred true)] := by
    intro t ht
    seg_fp ht using simp only [truncBits_ofNat hWord (by decide), compare, Option.getD_some,
      hTwo, hSkip, decide_true]
  intro s hs
  obtain ⟨v, hv, hV⟩ := hCalc s hs
  obtain ⟨hvA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) hv
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_911 true hV hV.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hV.1 (by simp) rfl hu
  exact ⟨u, run_comp hvA huA, hU.mono trivial⟩

private theorem rawBeforeWarmGate :
    ((kernel.code.drop 481).take (908 - 481)).all
      (fun i => loaderPipelineCutOp 481 908 1352 [1088] i.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem rawWarmBound {l : Launch} {g w : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hWord : w < 2 ^ 32) (hs : At s 481 [(1088, b32 w), (1091, b32 (countdown w))]) :
    loaderVisitsAt 1352 vs ≤ 54 := by
  by_cases hPos : 0 < w ∧ w < 2 ^ 31
  · exact loaderWarmPrefixFromPriming hw hPos.2 (by
      simpa [countdownPos hWord hPos.1] using hs)
  have hSkip : toSigned 32 (BitVec.ofNat 64 w) < 2 := by
    rw [toSignedWord hWord]
    split <;> omega
  have hAt : At s 481 [(1088, b32 w)] := hs.mono ⟨hs.2.2.2.2.1, trivial⟩
  apply loaderPrefixThroughCheckpoint 0 (F := [(1088, b32 w)]) (lower := 481) (cut := 908)
    (by decide) (by decide) (by decide) ⟨_, Flow.code_908, rfl⟩ rawBeforeWarmGate
    (budget := 54) _ hw (by rw [hAt.1]; decide) (ringShapeOfAt hAt) hAt.2.2.2.2
  intro t ts tv ht hWalk
  obtain ⟨u, hu, hU⟩ := rawWarmSkip (g := g) hWord hSkip t ht
  rcases loaderLocalWalkCut hu hWalk with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have h := loaderVisitsAt_le_length 1352 tv
    change loaderVisitsAt 1352 tv ≤ 54
    omega
  · have hp : (ringCounterSite 0).branch < u.pc := by rw [hU.1]; decide
    have hz := noLaterRingBranchVisits 0 hTail hp
    change loaderVisitsAt 1352 tail = 0 at hz
    change loaderVisitsAt 1352 tv ≤ 54
    rw [hTrace]
    have h := loaderVisitsAt_le_append 1352 pre tail
    omega

private theorem rawSteadySeed {l : Launch} {g w : Nat}
    (hWord : w < 2 ^ 32) (hNeg : toSigned 32 (BitVec.ofNat 64 w) < 0) :
    Seg kernel Assumptions.all l g 2 1353 [(1091, b32 w)] 1355
      [(7181, b32 0), (1091, b32 w)] := by
  intro s hs
  have hCore : Seg kernel [] l g 2 1353 [(1091, b32 w)] 1355
      [(7181, b32 0), (1091, b32 w)] := by
    have hZeroWord : truncBits 32 (BitVec.ofInt 64 0) = 0#64 := rfl
    have hTruncZero : truncBits 32 0#64 = 0#64 := rfl
    have hZeroSigned : toSigned 32 0#64 = 0 := rfl
    have hNine : toSigned 32 (truncBits 32 (BitVec.ofInt 64 9)) = 9 := rfl
    have hMin : (IntOp.min false == IntOp.max false) = false := rfl
    have hMax : (IntOp.max false == IntOp.max false) = true := rfl
    have hLt : ¬ 0 < toSigned 32 (BitVec.ofNat 64 w) := by omega
    intro t ht
    seg_fp ht using simp only [hMin, hMax, b32, truncBits_ofNat hWord (by decide), compare,
      kind_s_beq_s, Bool.false_eq_true, hZeroWord, hTruncZero, hZeroSigned, hNine,
      ↓reduceIte, decide_eq_true_eq,
      gt_iff_lt, hLt, show (0 : Int) < 9 by decide]
  obtain ⟨u, hu, hU⟩ := hCore s hs
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) hu
  exact ⟨u, huA, hU⟩

private theorem rawSteadySkip {l : Launch} {g w : Nat} (hWord : w < 2 ^ 32)
    (hNeg : toSigned 32 (BitVec.ofNat 64 w) < 0) :
    Seg kernel Assumptions.all l g 2 1384 [(7181, b32 0), (1091, b32 w)] 1744 [] := by
  have hNonpos : toSigned 32 (BitVec.ofNat 64 w) ≤ 0 := by omega
  have hZero : toSigned 32 (truncBits 32 (BitVec.ofNat 64 0)) = 0 := rfl
  have hCalc : Seg kernel [] l g 1 1384 [(7181, b32 0), (1091, b32 w)] 1385
      [(209, .pred true)] := by
    intro t ht
    seg_fp ht using simp only [truncBits_ofNat hWord (by decide), compare, Option.getD_some,
      hZero, ge_iff_le, hNonpos, decide_true]
  intro s hs
  obtain ⟨v, hv, hV⟩ := hCalc s hs
  obtain ⟨hvA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp) rfl hv
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1385 true hV hV.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hV.1 (by simp) rfl hu
  exact ⟨u, run_comp hvA huA, hU.mono trivial⟩

private theorem rawSteadyBeforeSeed :
    ((kernel.code.drop 481).take (1353 - 481)).all
      (fun i => loaderPipelineCutOp 481 1353 1743 [1091] i.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem rawSteadyBeforeGate :
    ((kernel.code.drop 1355).take (1384 - 1355)).all
      (fun i => loaderPipelineCutOp 1355 1384 1743 [7181, 1091] i.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

variable {l : Launch} {g w : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
include hw

private theorem rawSteadyGateBound (hWord : w < 2 ^ 32) (hNeg : toSigned 32 (BitVec.ofNat 64 w) < 0)
    (hs : At s 1384 [(7181, b32 0), (1091, b32 w)]) :
    loaderVisitsAt 1743 vs ≤ 2 := by
  obtain ⟨u, hu, hU⟩ := rawSteadySkip (g := g) hWord hNeg s hs
  rcases loaderLocalWalkCut hu hw with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have h := loaderVisitsAt_le_length 1743 vs
    omega
  · have hp : (ringCounterSite 1).branch < u.pc := by rw [hU.1]; decide
    have hz := noLaterRingBranchVisits 1 hTail hp
    change loaderVisitsAt 1743 tail = 0 at hz
    rw [hTrace]
    have h := loaderVisitsAt_le_append 1743 pre tail
    omega

private theorem rawSteadySeedBound (hWord : w < 2 ^ 32) (hNeg : toSigned 32 (BitVec.ofNat 64 w) < 0)
    (hs : At s 1353 [(1091, b32 w)]) :
    loaderVisitsAt 1743 vs ≤ 5 * 2 ^ 31 + 4 := by
  obtain ⟨u, hu, hU⟩ := rawSteadySeed (g := g) hWord hNeg s hs
  rcases loaderLocalWalkCut hu hw with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have h := loaderVisitsAt_le_length 1743 vs
    omega
  have h := loaderPrefixThroughCheckpoint 1 (F := [(7181, b32 0), (1091, b32 w)])
    (lower := 1355) (cut := 1384) (by decide) (by decide) (by decide)
    ⟨_, Flow.code_1384, rfl⟩ rawSteadyBeforeGate
    (fun ht hw => rawSteadyGateBound hw hWord hNeg ht) hTail
    (by rw [hU.1]; decide) (ringShapeOfAt hU) hU.2.2.2.2
  change loaderVisitsAt 1743 tail ≤ 2 at h
  rw [hTrace]
  have hTotal := loaderVisitsAt_le_append 1743 pre tail
  omega

private theorem rawSteadyBound (hWord : w < 2 ^ 32) (hs : At s 481 [(1091, b32 w)]) :
    loaderVisitsAt 1743 vs ≤ 5 * 2 ^ 31 + 4 := by
  by_cases hPos : w < 2 ^ 31
  · have h := loaderSteadyPrefixFromPriming hw hPos hs
    omega
  have hNeg : toSigned 32 (BitVec.ofNat 64 w) < 0 := by
    rw [toSignedWord hWord, ite_eq_right hPos]
    omega
  exact loaderPrefixThroughCheckpoint 1 (F := [(1091, b32 w)]) (lower := 481) (cut := 1353)
    (by decide) (by decide) (by decide) ⟨_, Flow.code_1353, rfl⟩ rawSteadyBeforeSeed
    (fun ht hw => rawSteadySeedBound hw hWord hNeg ht) hw
    (by rw [hs.1]; decide) (ringShapeOfAt hs) hs.2.2.2.2

/-- The actual priming countdown bounds both K/V rings for every 32-bit trip word. -/
theorem loaderRawRingBounds (hWord : w < 2 ^ 32) (hs : At s 477 [(1088, b32 w)]) :
    loaderVisitsAt 1352 vs ≤ 58 ∧ loaderVisitsAt 1743 vs ≤ 5 * 2 ^ 31 + 8 := by
  obtain ⟨u, hu, hU⟩ := rawCountdown (g := g) hWord s hs
  rcases loaderLocalWalkCut hu hw with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have hWarm := loaderVisitsAt_le_length 1352 vs
    have hSteady := loaderVisitsAt_le_length 1743 vs
    omega
  have hWarm := rawWarmBound hTail hWord hU
  have hWidth : countdown w < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hSteady := rawSteadyBound hTail hWidth
    (hU.mono ⟨hU.2.2.2.2.2.1, trivial⟩)
  rw [hTrace]
  have hw' := loaderVisitsAt_le_append 1352 pre tail
  have hs' := loaderVisitsAt_le_append 1743 pre tail
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader

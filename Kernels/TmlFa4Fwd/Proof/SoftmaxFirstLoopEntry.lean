-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstRound
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopCounter
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- The split gives the number of lower blocks eligible for the ordinary loop. -/
def firstPlainSplit (blocks biasCap : Nat) : Nat := blocks - min biasCap blocks

/-- The first visit has already consumed one block before either repeated loop. -/
def firstBiasedRepeats (blocks biasCap : Nat) : Nat := blocks - 1 - firstPlainSplit blocks biasCap

def firstLoopStable (blocks pastTile : Nat) (mx : Option ℝ) (old : ℝ) : List (Nat × Value) :=
  [(1226, b32 blocks), (1229, b32 (blocks-1)), (1225, b32 (pastTile+256)),
    (7256, scoreValue mx), (7257, fl old)]

private theorem loopInt32 {n : Nat} (hn : n < 2^31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2^64 := by omega
  have h32 : n < 2^32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left hn]

private theorem loopInt32_trunc {n : Nat} (hn : n < 2^31) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) = (n : Int) := by
  rw [truncBits_ofNat (show n < 2^32 by omega) (by decide), loopInt32 hn]

/-- The first visit's two counts determine the split, independently of FP32 data. -/
theorem firstLoopSplitCounts (l : Launch) (g blocks biasCap : Nat)
    (hBlocks : blocks < 2^31) (hCap : biasCap < 2^31) :
    Seg kernel Assumptions.all l g 3 5006 [(1228,b32 biasCap), (1226,b32 blocks)]
      5009 [(1359,b32 (firstPlainSplit blocks biasCap))] := by
  have hMinOp : (IntOp.min false == IntOp.max false) = false := rfl
  have hMaxOp : (IntOp.max false == IntOp.max false) = true := rfl
  have hSign : ((some IType.s : Option IType) == some IType.s) = true := rfl
  have hZero : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hMin : (if compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 biasCap))
        (truncBits 32 (BitVec.ofNat 64 blocks)) then truncBits 32 (BitVec.ofNat 64 biasCap)
        else truncBits 32 (BitVec.ofNat 64 blocks)) =
      BitVec.ofNat 64 (min biasCap blocks) := by
    have h32a : biasCap < 2^32 := by omega
    have h32b : blocks < 2^32 := by omega
    unfold compare
    rw [loopInt32_trunc hCap, loopInt32_trunc hBlocks]
    by_cases h : biasCap < blocks
    · have hc : (biasCap : Int) < blocks := by omega
      simp only [truncBits_ofNat h32a (by decide), truncBits_ofNat h32b (by decide),
        min_eq_left h.le]
      change (if decide ((biasCap : Int) < blocks) then _ else _) = _
      rw [decide_eq_true hc]
      rfl
    · have hc : ¬ (biasCap : Int) < blocks := by omega
      simp only [truncBits_ofNat h32a (by decide), truncBits_ofNat h32b (by decide),
        min_eq_right (le_of_not_gt h)]
      change (if decide ((biasCap : Int) < blocks) then _ else _) = _
      rw [decide_eq_false hc]
      rfl
  have hRest : firstPlainSplit blocks biasCap < 2^31 := by unfold firstPlainSplit; omega
  have hDiff :
      truncBits 32 (truncBits 32 (BitVec.ofNat 64 blocks) -
        truncBits 32 (BitVec.ofNat 64 (min biasCap blocks))) =
        BitVec.ofNat 64 (firstPlainSplit blocks biasCap) := by
    have hMinLE := min_le_right biasCap blocks
    norm_bits [firstPlainSplit]
  have hMax : (if compare .gt .s 32
      (truncBits 32 (BitVec.ofNat 64 (firstPlainSplit blocks biasCap)))
      (truncBits 32 (BitVec.ofInt 64 0)) then
      truncBits 32 (BitVec.ofNat 64 (firstPlainSplit blocks biasCap))
      else truncBits 32 (BitVec.ofInt 64 0)) =
      BitVec.ofNat 64 (firstPlainSplit blocks biasCap) := by
    unfold compare
    rw [loopInt32_trunc hRest, hZero,
      truncBits_ofNat (show firstPlainSplit blocks biasCap < 2^32 by omega) (by decide)]
    by_cases hz : firstPlainSplit blocks biasCap = 0
    · simp [hz]
      rfl
    · have hPos : (0 : Int) < firstPlainSplit blocks biasCap := by omega
      change (if decide (0 < (firstPlainSplit blocks biasCap : Int)) then _ else _) = _
      rw [decide_eq_true hPos]
      rfl
  intro t ht
  seg_fp ht using
    simp only [b32, hMinOp, hMaxOp, hSign, Bool.false_eq_true, ite_false, ite_true,
      hMin, hDiff, hMax]

def splitKeeps : List Nat := [1226,1229,1225,7256,7257]

/-- The split segment preserves the geometry and both numeric results already stored. -/
theorem firstLoopSplitFrame {l : Launch} {g : Nat} {t u : TState} (ht : t.pc = 5006)
    (hr : run kernel Assumptions.all l g 3 t = some u) :
    ∀ r ∈ splitKeeps, u.regs r = t.regs r := by
  refine fixedFrame (first := 5006) (stop := 5009) (kept := (· ∈ splitKeeps))
    ?_ ?_ (by omega) (by omega) hr
  · intro pc hLo hHi
    interval_cases pc
    · exact ⟨_,Flow.code_5006,rfl,rfl,by simp [BrxTarget],by decide⟩
    · exact ⟨_,Flow.code_5007,rfl,rfl,by simp [BrxTarget],by decide⟩
    · exact ⟨_,Flow.code_5008,rfl,rfl,by simp [BrxTarget],by decide⟩
  · intro pc hLo hHi
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega

private theorem firstLoopSplit (l : Launch) (g blocks biasCap pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (hBlocks : blocks < 2^31) (hCap : biasCap < 2^31) :
    Seg kernel Assumptions.all l g 3 5006
      ((1228, b32 biasCap) :: firstLoopStable blocks pastTile mx old)
      5009 ((1359, b32 (firstPlainSplit blocks biasCap)) ::
        firstLoopStable blocks pastTile mx old) := by
  intro t ht
  obtain ⟨u,hu,hU⟩ := (firstLoopSplitCounts l g blocks biasCap hBlocks hCap).apply
    (ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,trivial⟩)
  have hF := Epilogue.holdsSchedulerFrame ht.2.2.2.2.2 (firstLoopSplitFrame ht.1 hu)
    (fun _ h => by simpa [firstLoopStable, splitKeeps] using List.mem_map_of_mem (f := Prod.fst) h)
  exact ⟨u,hu,hU.mono ⟨hU.2.2.2.2.1,hF⟩⟩

private theorem firstLoopFloorInput (l : Launch) (g blocks split pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (hPast : pastTile + 256 < 2^31) :
    Seg kernel Assumptions.all l g 1 5009
      ((1359, b32 split) :: firstLoopStable blocks pastTile mx old)
      5010 ((3956, b32 pastTile) :: (1359, b32 split) ::
        firstLoopStable blocks pastTile mx old) := by
  intro t ht
  seg_fp ht using norm_bits

private theorem firstLoopFloor (l : Launch) (g blocks split pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (hPast : pastTile < 2^31) :
    Seg kernel Assumptions.all l g 10 5010
      ((3956, b32 pastTile) :: (1359, b32 split) :: firstLoopStable blocks pastTile mx old)
      5020 ((1360, b32 (pastTile / 128)) :: (1359, b32 split) ::
        firstLoopStable blocks pastTile mx old) := by
  have h32 : pastTile < 2^32 := by omega
  have hQuot : pastTile / 128 < 2^32 := by omega
  have hBound : pastTile / 128 * 128 < 2^32 := by omega
  have hS31 : (pastTile : Int) / 2^31 = 0 := by omega
  have hS7 : (pastTile : Int) / 2^7 = (pastTile / 128 : Nat) := by omega
  have s31 : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := rfl
  have s7 : min (truncBits 32 (BitVec.ofInt 64 7)).toNat 32 = 7 := rfl
  have s25 : (truncBits 32 (BitVec.ofInt 64 25)).toNat = 25 := rfl
  have z : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have z32 : truncBits 32 0 = 0 := rfl
  have zShift : (0 : BitVec 64) >>> 25 = 0 := rfl
  have h25 : ¬(25:Nat) ≥ 32 := by decide
  have aZero : BitVec.ofNat 64 pastTile + 0 = BitVec.ofNat 64 pastTile := BitVec.add_zero _
  have hZ : toSigned 32 0 = 0 := rfl
  have hNN : ¬(pastTile : Int) < 0 := by omega
  have hM : truncBits 32 (BitVec.ofInt 64 (-128)) = BitVec.ofNat 64 4294967168 := rfl
  have hBits : (pastTile &&& 4294967168) = pastTile / 128 * 128 := by
    have hDiv : (pastTile &&& 4294967168) / 128 = pastTile / 128 := by
      rw [show 128 = 2 ^ 7 from rfl, Nat.and_div_two_pow]
      change pastTile / 128 &&& (2 ^ 25 - 1) = pastTile / 128
      exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
    have hMod : (pastTile &&& 4294967168) % 128 = 0 := by
      rw [show 128 = 2 ^ 7 from rfl, Nat.and_mod_two_pow]
      simp
    omega
  have hValA : (BitVec.ofNat 64 pastTile).toNat = pastTile := toNat_ofNat_lt (by omega)
  have hValB : (BitVec.ofNat 64 (pastTile / 128 * 128)).toNat = pastTile / 128 * 128 :=
    toNat_ofNat_lt (by omega)
  let rem := decide (pastTile ≠ pastTile / 128 * 128)
  have hRemPred : decide ((pastTile : Int) ≠ (pastTile / 128 * 128 : Nat)) = rem := by
    unfold rem
    rw [decide_eq_decide]
    exact not_congr Int.ofNat_inj
  have hFirst : Seg kernel Assumptions.all l g 7 5010
      ((3956, b32 pastTile) :: (1359, b32 split) :: firstLoopStable blocks pastTile mx old)
      5017 ((3960, b32 (pastTile / 128)) :: (627, .pred rem) :: (628, .pred false) ::
        (1359, b32 split) :: firstLoopStable blocks pastTile mx old) := by
    intro t ht
    seg_fp ht using
      simp only [b32, s31, s7, s25, ite_eq_right h25, hS31, hS7, z, z32, zShift, aZero,
        truncBits_ofNat h32 (by decide), truncBits_ofNat hQuot (by decide),
        truncBits_ofNat hBound (by decide), BitVec.ofInt_natCast, compare, loopInt32 hPast,
        hZ, hNN, decide_false, hM, ← BitVec.ofNat_and, hBits, hValA, hValB, Option.getD_some,
        rem]
      all_goals exact congrArg Value.pred hRemPred
  have hLast : Seg kernel Assumptions.all l g 3 5017
      ((3960, b32 (pastTile / 128)) :: (627, .pred rem) :: (628, .pred false) ::
        (1359, b32 split) :: firstLoopStable blocks pastTile mx old)
      5020 ((1360, b32 (pastTile / 128)) :: (1359, b32 split) ::
        firstLoopStable blocks pastTile mx old) := by
    generalize h : rem = b
    cases b <;> intro t ht <;> seg_fp ht using norm_bits
  exact hFirst.comp hLast

def loopChoiceFacts (blocks split pastTile : Nat) (mx : Option ℝ) (old : ℝ)
    (phase scorePhase : Bool) :
    List (Nat × Value) :=
  (1360, b32 (pastTile/128)) :: (1359, b32 split) :: (7253, b32 scorePhase.toNat) :: (7258, b32
    phase.toNat) ::
    firstLoopStable blocks pastTile mx old

def firstLoopChoiceFacts (blocks split pastTile : Nat) (mx : Option ℝ) (old : ℝ) :
    List (Nat × Value) :=
  loopChoiceFacts blocks split pastTile mx old true true

def firstBiasedFacts (blocks split pastTile : Nat) (mx : Option ℝ) (old : ℝ) :
    List (Nat × Value) :=
  [(7248, b32 (2^32 - (blocks - split))), (7249, b32 (blocks-1)),
    (1361, b32 (pastTile/128)), (7251, scoreValue mx), (7250, b32 1)] ++
    firstLoopChoiceFacts blocks split pastTile mx old

def plainLoopFacts (p : Params) (blocks split pastTile : Nat) (mx : Option ℝ) (old : ℝ)
    (phase scorePhase : Bool) :
    List (Nat × Value) :=
  [(7254, b32 (2^32-split)), (7255, scoreValue mx), (7133, b32 p.scaleLog2Bits),
    (8692, joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits))] ++
    loopChoiceFacts blocks split pastTile mx old phase scorePhase

def firstPlainFacts (p : Params) (blocks split pastTile : Nat) (mx : Option ℝ) (old : ℝ) :
    List (Nat × Value) :=
  plainLoopFacts p blocks split pastTile mx old true true

private theorem firstLoopDiffTest {blocks split : Nat}
    (hb : 0 < blocks) (hb32 : blocks < 2^31) (hsplit : split < blocks) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1)) -
      truncBits 32 (BitVec.ofNat 64 split)) = BitVec.ofNat 64 (blocks - 1 - split) ∧
    compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1 - split)))
      (truncBits 32 (BitVec.ofInt 64 1)) = decide (blocks - 1 - split = 0) := by
  have hDiff : truncBits 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1)) -
      truncBits 32 (BitVec.ofNat 64 split)) = BitVec.ofNat 64 (blocks - 1 - split) := by
    norm_bits
  have hTest : compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1 - split)))
      (truncBits 32 (BitVec.ofInt 64 1)) = decide (blocks - 1 - split = 0) := by
    change decide (toSigned 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1 - split))) <
      (1 : Int)) = _
    rw [loopInt32_trunc (by omega), decide_eq_decide]
    omega
  exact ⟨hDiff,hTest⟩

/-- Bias-loop entry is decided by the two countdown limits. -/
theorem firstLoopCountDecision (l : Launch) (g blocks split : Nat)
    (hb : 0 < blocks) (hb32 : blocks < 2^31) (hsplit : split < blocks) :
    Seg kernel Assumptions.all l g 4 5020
      [(1226,b32 blocks), (1229,b32 (blocks-1)), (1359,b32 split)]
      5024 [(630,.pred (decide (blocks-1-split = 0))), (1226,b32 blocks),
        (1229,b32 (blocks-1)), (1359,b32 split)] := by
  obtain ⟨hDiff,hTest⟩ := firstLoopDiffTest hb hb32 hsplit
  intro t ht
  seg_fp ht using
    simp only [hDiff, Option.getD_some, hTest]

private theorem firstLoopTest (l : Launch) (g blocks split pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (hb : 0 < blocks) (hb32 : blocks < 2^31) (hsplit : split < blocks) :
    Seg kernel Assumptions.all l g 4 5020
      ((1360, b32 (pastTile / 128)) :: (1359, b32 split) :: firstLoopStable blocks pastTile mx old)
      5024 ((630, .pred (decide (blocks - 1 - split = 0))) ::
        firstLoopChoiceFacts blocks split pastTile mx old) := by
  obtain ⟨hDiff,hTest⟩ := firstLoopDiffTest hb hb32 hsplit
  intro t ht
  seg_fp ht using
    simp only [b32, hDiff, Option.getD_some, hTest]
    all_goals rfl

private theorem firstBiasedStart (l : Launch) (g blocks split pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (hsplit : split < blocks) (hb : blocks < 2^31)
    (hPast : pastTile < 2^31) :
    Seg kernel Assumptions.all l g 7 5025 (firstLoopChoiceFacts blocks split pastTile mx old)
      5032 (firstBiasedFacts blocks split pastTile mx old) := by
  have hDiff : truncBits 32 (truncBits 32 (BitVec.ofNat 64 split) -
      truncBits 32 (BitVec.ofNat 64 blocks)) = BitVec.ofNat 64 (2^32 - (blocks - split)) := by
    norm_bits
  have hMax (n : Nat) (hn : n < 2^31) : (if compare .gt .s 32
        (truncBits 32 (BitVec.ofNat 64 n)) (truncBits 32 (BitVec.ofInt 64 0)) then
        truncBits 32 (BitVec.ofNat 64 n) else truncBits 32 (BitVec.ofInt 64 0)) =
      BitVec.ofNat 64 n := by
    by_cases h : n = 0
    · subst n
      rfl
    · change (if decide (toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) > (0 : Int))
          then _ else _) = _
      rw [loopInt32_trunc hn, decide_eq_true (show (0 : Int) < n by omega),
        truncBits_ofNat (show n < 2^32 by omega) (by decide)]
      rfl
  have hM := hMax (pastTile / 128) (by omega)
  have hMaxOp : (IntOp.max false == IntOp.max false) = true := rfl
  have hS : ((some IType.s : Option IType) == some IType.s) = true := rfl
  cases mx <;> intro t ht <;> simp only [firstBiasedFacts, List.cons_append, List.nil_append] <;>
    seg_fp ht using
      simp only [b32, hDiff, hMaxOp, hS, hM, ite_true]
      all_goals rfl

/-- The actual first-round continuation either initializes the bias loop or branches to
the ordinary-loop decision, carrying the initial maximum, denominator and phase. -/
theorem firstLoopEntryLocal {l : Launch} {g : Nat} {t : TState}
    (blocks biasCap pastTile : Nat) (mx : Option ℝ) (old : ℝ)
    (hb : 0 < blocks) (hb32 : blocks < 2^31) (hc : 0 < biasCap) (hc32 : biasCap < 2^31)
    (hPast : pastTile + 256 < 2^31)
    (ht : At t 5006 ((1228, b32 biasCap) :: firstLoopStable blocks pastTile mx old)) :
    let split := firstPlainSplit blocks biasCap
    let repeats := firstBiasedRepeats blocks biasCap
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (if repeats = 0 then At u 6654 (firstLoopChoiceFacts blocks split pastTile mx old)
       else At u 5032 (firstBiasedFacts blocks split pastTile mx old)) := by
  let split := firstPlainSplit blocks biasCap
  have hSplit : split < blocks := by unfold split firstPlainSplit; omega
  obtain ⟨u, huRun, hu⟩ :=
    (firstLoopSplit l g blocks biasCap pastTile mx old hb32 hc32).apply ht
  obtain ⟨v, hvRun, hv⟩ := (firstLoopFloorInput l g blocks split pastTile mx old hPast).apply hu
  obtain ⟨w, hwRun, hw⟩ := (firstLoopFloor l g blocks split pastTile mx old (by omega)).apply hv
  obtain ⟨x, hxRun, hx⟩ := (firstLoopTest l g blocks split pastTile mx old hb hb32 hSplit).apply hw
  let repeats := firstBiasedRepeats blocks biasCap
  have hPick : x.regs 630 = some (.pred (decide (repeats = 0))) := hx.2.2.2.2.1
  have hx' : At x 5024 (firstLoopChoiceFacts blocks split pastTile mx old) :=
    hx.mono hx.2.2.2.2.2
  obtain ⟨y, hyRun, hy⟩ := run_bra (A := Assumptions.all) (L := l) (g := g)
    Flow.code_5024 (decide (repeats = 0)) hx' hPick (fun a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (maxSeg (by decide))
  have hFirst := run_comp (run_comp (run_comp (run_comp huRun hvRun) hwRun) hxRun) hyRun
  have hyTail := run_rtg hFirst
  by_cases hz : repeats = 0
  · refine ⟨y, hyTail, ?_⟩
    have hz' : firstBiasedRepeats blocks biasCap = 0 := hz
    simpa only [hz', hz, ite_true, decide_true] using hy
  · have hy' : At y 5025 (firstLoopChoiceFacts blocks split pastTile mx old) := by
      simpa only [decide_eq_false hz, Bool.false_eq_true, ite_false] using hy
    obtain ⟨z, hzRun, hzAt⟩ :=
      (firstBiasedStart l g blocks split pastTile mx old hSplit hb32 (by omega)).apply hy'
    refine ⟨z, hyTail.trans (run_rtg hzRun), ?_⟩
    have hz' : firstBiasedRepeats blocks biasCap ≠ 0 := hz
    simpa only [hz', ite_false] using hzAt

theorem firstLoopEntryTrace {l : Launch} {g : Nat} {t : TState} {es : List Event}
    (blocks biasCap pastTile : Nat) (mx : Option ℝ) (old : ℝ)
    (hb : 0 < blocks) (hb32 : blocks < 2^31) (hc : 0 < biasCap) (hc32 : biasCap < 2^31)
    (hPast : pastTile + 256 < 2^31)
    (ht : At t 5006 ((1228, b32 biasCap) :: firstLoopStable blocks pastTile mx old))
    (hRun : Run kernel Assumptions.all l g t es none) :
    let split := firstPlainSplit blocks biasCap
    let repeats := firstBiasedRepeats blocks biasCap
    ∃ u, Run kernel Assumptions.all l g u es none ∧
      (if repeats = 0 then At u 6654 (firstLoopChoiceFacts blocks split pastTile mx old)
       else At u 5032 (firstBiasedFacts blocks split pastTile mx old)) := by
  obtain ⟨u,hLocal,hAt⟩ := firstLoopEntryLocal (l := l) (g := g) blocks biasCap pastTile mx old
    hb hb32 hc hc32 hPast ht
  exact ⟨u,hRun.after_local hLocal,hAt⟩

private theorem plainLoopTest (l : Launch) (g blocks split pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (phase scorePhase : Bool) (hb : blocks < 2^31) (hs : split < blocks) :
    Seg kernel Assumptions.all l g 2 6654 (loopChoiceFacts blocks split pastTile mx old phase
      scorePhase)
      6656 ([(643, .pred (decide (split = 0))), (1491, b32 split)] ++
        loopChoiceFacts blocks split pastTile mx old phase scorePhase) := by
  have hMinOp : (IntOp.min false == IntOp.max false) = false := rfl
  have hSign : ((some IType.s : Option IType) == some IType.s) = true := rfl
  have hMin : compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1)))
      (truncBits 32 (BitVec.ofNat 64 split)) = false := by
    change decide (toSigned 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1))) <
      toSigned 32 (truncBits 32 (BitVec.ofNat 64 split))) = false
    rw [loopInt32_trunc (by omega), loopInt32_trunc (by omega)]
    exact decide_eq_false (by omega)
  have hTest : compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 split))
      (truncBits 32 (BitVec.ofInt 64 1)) = decide (split = 0) := by
    change decide (toSigned 32 (truncBits 32 (BitVec.ofNat 64 split)) < (1 : Int)) = _
    rw [loopInt32_trunc (by omega), decide_eq_decide]
    omega
  intro t ht
  simp only [List.cons_append, List.nil_append]
  seg_fp ht using
    simp only [b32, hMinOp, hSign, Bool.false_eq_true, ite_false, ite_true, hMin,
      Option.getD_some]
    simp only [truncBits_ofNat (show split < 2^32 by omega) (by decide)] at hTest ⊢
    all_goals rw [hTest]

private def plainScaleLoad : Op := .mem {
  kind := .load
  space := some .param
  sem := .weak
  elem := .int .b 32
  addr := ⟨.param (param 12) false, 0⟩
  dsts := [some 7133] }

private theorem plainScaleCode : kernel.code[6658]? = some ⟨none, plainScaleLoad⟩ := by
  have hName : param 12 =
      "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_obje\
      ct_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf\
      16gmemalign16o1i64div8_0_param_12" := by
    unfold param
    decide +kernel
  rw [Flow.code_6658, plainScaleLoad, hName]

variable {p : Params} {l : Launch} {m : Mem0}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem plainLoopPrepare (hp : Pre p l m) (g blocks split pastTile : Nat) (mx : Option ℝ)
    (old : ℝ) (phase scorePhase : Bool) (hs : 0 < split) (hb : split < 2^31) :
    Seg kernel Assumptions.all l g 4 6657 ((1491, b32 split) ::
      loopChoiceFacts blocks split pastTile mx old phase scorePhase)
      6661 (plainLoopFacts p blocks split pastTile mx old phase scorePhase) := by
  have hArg : (12, p.scaleLog2Bits) ∈ p.scalarWords := by simp [Params.scalarWords]
  have hBits := (hp.values _ hArg).1
  have hParam := (hp.values _ hArg).2
  have hNeg : truncBits 32 (-truncBits 32 (BitVec.ofNat 64 split)) =
      BitVec.ofNat 64 (2^32-split) := by
    norm_bits
  let frame := loopChoiceFacts blocks split pastTile mx old phase scorePhase
  have hFirst : Seg kernel Assumptions.all l g 1 6657 ((1491, b32 split) :: frame) 6658
      ((7254, b32 (2^32-split)) :: frame) := by
    intro t ht
    simp only [frame] at ht ⊢
    seg_fp ht using simp only [b32, hNeg]
  have hLoad : Seg kernel Assumptions.all l g 1 6658 ((7254, b32 (2^32-split)) :: frame) 6659
      ((7133, b32 p.scaleLog2Bits) :: (7254, b32 (2^32-split)) :: frame) := by
    intro t ht
    let u := next (setReg t 7133 (b32 p.scaleLog2Bits))
    have hu : run kernel Assumptions.all l g 1 t = some u := by
      apply run_local plainScaleCode rfl ht
      rw [Assumptions.execLocalA_all_eq_numeric,
        Assumptions.execLocalA_eq_nil (ht.1 ▸ (by decide)) rfl, execLocalA_nil]
      change (match l.params (param 12) with
        | some x => Except.ok (next (setReg t 7133 (MemExt.same.extendBits 32 x)))
        | none => Except.error Fault.badParam) = _
      rw [hParam]
      change Except.ok (next (setReg t 7133
        (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.scaleLog2Bits))))) = _
      rw [truncBits_ofNat hBits (by decide)]
      rfl
    exact ⟨u, hu, ht.set (by
      intro pair hm
      simp only [frame, loopChoiceFacts, firstLoopStable, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)⟩
  have hLast : Seg kernel Assumptions.all l g 2 6659
      ((7133, b32 p.scaleLog2Bits) :: (7254, b32 (2^32-split)) :: frame) 6661
      (plainLoopFacts p blocks split pastTile mx old phase scorePhase) := by
    cases mx <;> intro t ht <;>
      simp only [frame, plainLoopFacts, List.cons_append, List.nil_append] at ht ⊢ <;>
      seg_fp ht using rfl
  exact (hFirst.comp hLoad).comp hLast

/-- At the first-round ordinary-loop decision, the actual branch starts the ordinary
loop with its maximum, denominator and negative count, or reaches the final suffix. -/
theorem plainLoopEntryLocal (hp : Pre p l m) {g : Nat} {t : TState} (blocks split pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (phase scorePhase : Bool) (hb : blocks < 2^31) (hs : split < blocks)
    (ht : At t 6654 (loopChoiceFacts blocks split pastTile mx old phase scorePhase)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (if split = 0 then
        At u 7605 ((1491, b32 split) :: loopChoiceFacts blocks split pastTile mx old phase
          scorePhase)
       else At u 6661 (plainLoopFacts p blocks split pastTile mx old phase scorePhase)) := by
  obtain ⟨v, hvRun, hv⟩ := (plainLoopTest l g blocks split pastTile mx old phase scorePhase hb
    hs).apply ht
  obtain ⟨w, hwRun, hw⟩ := run_bra (A := Assumptions.all) (L := l) (g := g)
    Flow.code_6656 (decide (split = 0)) (hv.mono hv.2.2.2.2.2) hv.2.2.2.2.1
    (fun a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (maxSeg (by decide))
  have hwTail := run_rtg (run_comp hvRun hwRun)
  by_cases h0 : split = 0
  · refine ⟨w, hwTail, ?_⟩
    change At w (if decide (split = 0) then 7605 else 6657)
      ((1491, b32 split) :: loopChoiceFacts blocks split pastTile mx old phase scorePhase) at hw
    simpa only [h0, ite_true, decide_true] using hw
  · have hw' : At w 6657
        ((1491, b32 split) :: loopChoiceFacts blocks split pastTile mx old phase scorePhase) := by
      change At w (if decide (split = 0) then 7605 else 6657)
        ((1491, b32 split) :: loopChoiceFacts blocks split pastTile mx old phase scorePhase) at hw
      simpa only [decide_eq_false h0, Bool.false_eq_true, ite_false] using hw
    obtain ⟨u, huRun, hu⟩ :=
      (plainLoopPrepare hp g blocks split pastTile mx old phase scorePhase
        (by omega) (by omega)).apply hw'
    exact ⟨u, hwTail.trans (run_rtg huRun), by simpa only [h0, ite_false] using hu⟩

theorem firstPlainEntryLocal (hp : Pre p l m) {g : Nat} {t : TState} (blocks split pastTile : Nat)
    (mx : Option ℝ) (old : ℝ) (hb : blocks < 2^31) (hs : split < blocks)
    (ht : At t 6654 (firstLoopChoiceFacts blocks split pastTile mx old)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (if split = 0 then
        At u 7605 ((1491, b32 split) :: firstLoopChoiceFacts blocks split pastTile mx old)
       else At u 6661 (firstPlainFacts p blocks split pastTile mx old)) :=
  plainLoopEntryLocal hp blocks split pastTile mx old true true hb hs ht

theorem firstPlainEntryTrace (hp : Pre p l m) {g : Nat} {t : TState} {es : List Event}
    (blocks split pastTile : Nat) (mx : Option ℝ) (old : ℝ) (hb : blocks < 2^31)
    (hs : split < blocks) (ht : At t 6654 (firstLoopChoiceFacts blocks split pastTile mx old))
    (hRun : Run kernel Assumptions.all l g t es none) :
    ∃ u, Run kernel Assumptions.all l g u es none ∧
      (if split = 0 then
        At u 7605 ((1491, b32 split) :: firstLoopChoiceFacts blocks split pastTile mx old)
       else At u 6661 (firstPlainFacts p blocks split pastTile mx old)) := by
  obtain ⟨u,hLocal,hAt⟩ := firstPlainEntryLocal (l := l) (g := g) hp blocks split pastTile mx old
    hb hs ht
  exact ⟨u,hRun.after_local hLocal,hAt⟩

theorem initialBiasedDistance {blocks split : Nat}
    (hb : blocks < 2^31) (hMore : split + 1 < blocks) :
    scoreLoopDistance .biased (2^32 - (blocks - split)) = blocks - 1 - split := by
  have h : 2^32 - (blocks - split) < (scoreLoopSite .biased).sentinel := by
    change 2^32 - (blocks - split) < 2^32 - 1
    omega
  unfold scoreLoopDistance
  rw [ite_eq_left h]
  change 2^32 - 1 - (2^32 - (blocks - split)) = _
  omega

theorem initialPlainDistance {split : Nat} (hPos : 0 < split) (hBound : split < 2^31) :
    scoreLoopDistance .plain (2^32 - split) = split := by
  simp only [scoreLoopDistance, scoreLoopSite, Nat.not_lt_zero, ite_false, Nat.add_zero]
  omega

/-- The first denominator hands off to the appropriate repeated loop or the exit suffix.
The stored maximum, denominator and parity bits are carried into that actual continuation. -/
theorem firstRoundLoopTrace {X : Execution} (hp : Pre p l m) (warp : Fin 8)
    {g j batch head row blocks biasCap pastTile : Nat} (hb : 0 < blocks) (hb32 : blocks < 2^31)
    (hc : 0 < biasCap) (hc32 : biasCap < 2^31) (hPast : pastTile + 256 < 2^31)
    (hRound : FirstRoundProgress p l X warp g j batch head row blocks biasCap pastTile) :
    let mx := scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c))
      (List.range 128)
    let reference := firstReference p batch head row blocks
    let mass := (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount batch row) blocks 0
      (weight p batch head row)
    let split := firstPlainSplit blocks biasCap
    let biased := firstBiasedRepeats blocks biasCap
    ∃ u leader failed,
      let post := if laneOf l g = leader then j + 12 else j + 11
      Run kernel Assumptions.all l g u ((X.tr g).drop (post + failed + 1)) none ∧
      (if biased = 0 then
        if split = 0 then
          At u 7605 ((1491, b32 split) :: firstLoopChoiceFacts blocks split pastTile mx mass)
        else At u 6661 (firstPlainFacts p blocks split pastTile mx mass)
       else At u 5032 (firstBiasedFacts blocks split pastTile mx mass)) := by
  obtain ⟨s, _, _, leader, failed, _, _, _, _, hs, hRun⟩ := hRound
  let mx := scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c))
    (List.range 128)
  let reference := firstReference p batch head row blocks
  let mass := (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount batch row) blocks 0
    (weight p batch head row)
  have fields : Holds s.regs
      [(7257, fl mass), (1225, b32 (pastTile+256)), (1226, b32 blocks), (1228, b32 biasCap),
        (1229, b32 (blocks-1)), (7256, scoreValue mx)] := hs.2.2.2.2
  obtain ⟨hMass, hPastReg, hBlocksReg, hCapReg, hLastReg, hMx, _⟩ := fields
  have hState : At s 5006 ((1228, b32 biasCap) :: firstLoopStable blocks pastTile mx mass) :=
    hs.mono ⟨hCapReg, hBlocksReg, hLastReg, hPastReg, hMx, hMass, trivial⟩
  obtain ⟨v, hvRun, hv⟩ :=
    firstLoopEntryTrace blocks biasCap pastTile mx mass hb hb32 hc hc32 hPast hState hRun
  by_cases hz : firstBiasedRepeats blocks biasCap = 0
  · have hSplit : firstPlainSplit blocks biasCap < blocks := by unfold firstPlainSplit; omega
    have hv' : At v 6654
        (firstLoopChoiceFacts blocks (firstPlainSplit blocks biasCap) pastTile mx mass) := by
      simpa only [hz, ite_true] using hv
    obtain ⟨u, huRun, hU⟩ := firstPlainEntryTrace hp blocks (firstPlainSplit blocks biasCap)
      pastTile mx mass hb32 hSplit hv' hvRun
    exact ⟨u, leader, failed, huRun, by simpa only [hz, ite_true] using hU⟩
  · exact ⟨v, leader, failed, hvRun, by simpa only [hz, ite_false] using hv⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax

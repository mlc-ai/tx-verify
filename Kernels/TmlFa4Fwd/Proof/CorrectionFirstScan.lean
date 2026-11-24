-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFirstTiles
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroup
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Lemmas.Flow.WarpScan
import Kernels.TmlFa4Fwd.Flow.Code.Part121

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def correctionScanPc (stage : Fin 5) : Nat := 7781 + 4 * stage.val

def correctionScanSrc : Fin 5 → Nat
  | 0 => 7270
  | 1 => 5878
  | 2 => 5881
  | 3 => 5884
  | 4 => 5887

def correctionScanDst (stage : Fin 5) : Nat := 5876 + 3 * stage.val

def correctionScanResult (stage : Fin 5) : Nat :=
  if stage.val = 4 then 7271 else 5878 + 3 * stage.val

theorem correctionScanCode (stage : Fin 5) :
    kernel.code[correctionScanPc stage]? = some ⟨none, .warp
      { kind := .shfl .up
        ty := some (.int .b 32)
        dsts := [some (correctionScanDst stage)]
        srcs := [.reg (correctionScanSrc stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0]
        mask := some (.imm (-1)) }⟩ := by
  fin_cases stage
  · exact Flow.code_7781
  · exact Flow.code_7785
  · exact Flow.code_7789
  · exact Flow.code_7793
  · exact Flow.code_7797

variable {p : Params}

/-- Each of the first pass's five scan rounds shuffles the previous partial sum by the exact
doubling offset. -/
theorem correctionScanTemplate {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) (t : TState)
    (stage : Fin 5) (sum : Nat) (hpc : t.pc = correctionScanPc stage) (hf : t.fault = none)
    (hv : t.regs (correctionScanSrc stage) = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (correctionScanDst stage) value))) := by
  have hb : l.block % 32 = 0 := by rw [hp.block]
  have hc := correctionScanCode stage
  rw [← hpc] at hc
  rw [out_event hf hc rfl rfl]
  change Out.ev (shflTmpl l g t .up (correctionScanDst stage) none (.reg (correctionScanSrc stage))
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

private def correctionScanGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2 ^ stage.val ≤ lane)

private theorem correctionScanCompare (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) :
    Seg kernel [] l g 1 (correctionScanPc stage + 1)
      [(1616, b32 lane), (correctionScanSrc stage, b32 left), (correctionScanDst stage, b32 recv)]
      (correctionScanPc stage + 2)
      [(689 + stage.val, .pred (correctionScanGuard stage lane)),
       (correctionScanSrc stage, b32 left), (correctionScanDst stage, b32 recv)] := by
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
      simp only [correctionScanGuard, Nat.reduceEqDiff, ↓reduceIte, compare, Option.getD_some,
        truncBits_ofNat hLane (by decide), toNat_ofNat_lt hLane64,
        Value.pred.injEq, decide_eq_decide, hz, h1, h3, h7, h15]
      all_goals omega

private theorem correctionScanSelect (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (correctionScanPc stage + 2)
      [(689 + stage.val, .pred (correctionScanGuard stage lane)),
       (correctionScanSrc stage, b32 left), (correctionScanDst stage, b32 recv)]
      (correctionScanPc stage + 4)
      [(correctionScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  have hLeft : left < 2 ^ 32 := by omega
  have hRecv : recv < 2 ^ 32 := by omega
  by_cases h : 2 ^ stage.val ≤ lane
  · have hp : correctionScanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [correctionScanGuard, hst, show lane ≠ 0 by omega]
      · simp [correctionScanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_left h]
  · have hp : correctionScanGuard stage lane = decide (stage.val = 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [correctionScanGuard, hst, show lane = 0 by omega]
      · simp [correctionScanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_right h]

/-- The three local instructions after an up-shuffle implement its guarded addition. -/
theorem correctionScanCombine (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 3 (correctionScanPc stage + 1)
      [(1616, b32 lane), (correctionScanSrc stage, b32 left), (correctionScanDst stage, b32 recv)]
      (correctionScanPc stage + 4)
      [(correctionScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] :=
  (correctionScanCompare stage l g hl).comp (correctionScanSelect stage l g hl hsum)

/-- The shuffle source given by PTX and the decoded local addition implement one round of the
inclusive prefix scan. -/
theorem correctionScanFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hl : lane < 32)
    (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 3 (correctionScanPc stage + 1)
      [(1616, b32 lane), (correctionScanSrc stage, b32 (prefixWindow xs (2 ^ stage.val) lane)),
       (correctionScanDst stage,
         b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (correctionScanPc stage + 4)
      [(correctionScanResult stage, b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := correctionScanCombine stage l g hl hsum
  rw [Epilogue.firstScanSource] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

def correctionScanFacts (p : Params) (l : Launch) (g stage lane : Nat) :
    List (Nat × Value) :=
  (if h : stage < 5 then correctionScanSrc ⟨stage, h⟩ else 7271,
    b32 (prefixWindow (groupLaneTiles p 0) (2 ^ stage) lane)) ::
  firstCorrectionScanFacts p l (warpLane l g lane)

private theorem firstCorrectionFresh {l : Launch} {g : Nat} (stage : Fin 5) (lane : Nat)
    (_ : lane < 32) (pair : Nat × Value) (hm : pair ∈ correctionScanFacts p l g stage.val lane) :
    pair.1 ≠ correctionScanDst stage := by
  have hm' := List.mem_map_of_mem (f := Prod.fst) hm
  intro he
  rw [he] at hm'
  have hDisjoint :
      correctionScanDst stage ∉ (correctionScanFacts p l g stage.val lane).map Prod.fst := by
    fin_cases stage <;> exact of_decide_eq_true rfl
  exact hDisjoint hm'

private theorem firstCorrectionOut {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g shuffles votes : Nat} (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g (correctionScanPc stage)
      (correctionScanFacts p l g stage.val) shuffles votes ends) (lane : Nat) (hl : lane < 32) :
    let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
    out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
      .ev (.shfl .up (b32 (part lane)) (2 ^ stage.val) 0
        (fun v _ => next (setReg (cur.state lane) (correctionScanDst stage) v))) := by
  dsimp only
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  have ht := cur.checkpoint lane hl
  have hreg : (cur.state lane).regs (correctionScanSrc stage) = some (b32 (part lane)) := by
    have hMem := ht.2.2.2.2
    unfold correctionScanFacts at hMem
    simp only [dite_eq_left stage.isLt] at hMem
    exact hMem.1
  rw [correctionSchedulerOut (by rw [ht.1]; have := stage.isLt; simp [correctionScanPc]; omega)
    (by rw [ht.1]; have := stage.isLt; simp [correctionScanPc]; omega)]
  exact correctionScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1 hreg

private theorem firstCorrectionFoldLocal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g shuffles votes : Nat} (hg : g < l.threads) (stage : Fin 5) {ends : Nat → Option TState}
    (read : SchedulerWarpAt l X g (correctionScanPc stage + 1)
      (fun lane => (correctionScanDst stage, b32 (prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
        (shflSource .up lane (2 ^ stage.val) 0).1)) :: correctionScanFacts p l g stage.val lane)
      shuffles votes ends) :
    ∀ lane < 32, ∃ u, Relation.ReflTransGen
      (Tau kernel Assumptions.all l (warpLane l g lane)) (read.state lane) u ∧
      At u (correctionScanPc stage + 4) (correctionScanFacts p l g (stage.val + 1) lane) := by
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  intro lane hl
  let thread := warpLane l g lane
  let regs := (firstCorrectionScanFacts p l thread).map Prod.fst
  have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hAt := read.checkpoint lane hl
  have hCarry : Holds (read.state lane).regs (firstCorrectionScanFacts p l thread) := by
    have h := hAt.2.2.2.2.2
    unfold correctionScanFacts at h
    simp only [dite_eq_left stage.isLt] at h
    exact h.2
  have hReg : (read.state lane).regs 1616 = some (b32 lane) := by
    have h := holds_mem hCarry (by simp [firstCorrectionScanFacts, firstShuffleFacts] :
      (1616, b32 (laneOf l thread)) ∈ firstCorrectionScanFacts p l thread)
    change laneOf l thread = lane at hLane
    rw [hLane] at h
    exact h
  have hFoldAt : At (read.state lane) (correctionScanPc stage + 1)
      [(1616, b32 lane), (correctionScanSrc stage, b32 (part lane)),
       (correctionScanDst stage, b32 (part (shflSource .up lane (2 ^ stage.val) 0).1))] := by
    have h := hAt.2.2.2.2.2
    unfold correctionScanFacts at h
    simp only [dite_eq_left stage.isLt] at h
    exact hAt.mono ⟨hReg, h.1, hAt.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := correctionScanFold stage l thread _ hl
    (groupPrefixOperands_fit hp (Nat.zero_le p.batch) hl stage) _ hFoldAt
  obtain ⟨huA, hFrame⟩ := correctionLinear (regs := regs)
    (by have := stage.isLt; simp [correctionScanPc]; omega)
    (by have := stage.isLt; simp [correctionScanPc]; omega) hFoldAt.1
    (by fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
  have hSaved := holdsSchedulerFrame hCarry hFrame (fun _ h => List.mem_map_of_mem h)
  have hNextReg : (if h : stage.val + 1 < 5 then
      correctionScanSrc ⟨stage.val + 1, h⟩ else 7271) = correctionScanResult stage := by
    fin_cases stage <;> rfl
  have hNextWidth : 2 ^ (stage.val + 1) = 2 * 2 ^ stage.val := by
    rw [Nat.pow_succ, Nat.mul_comm]
  refine ⟨u, run_rtg huA, hU.mono ?_⟩
  unfold correctionScanFacts
  rw [hNextReg, hNextWidth]
  exact ⟨hU.2.2.2.2.1, hSaved⟩

private theorem firstCorrectionFold {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    (stage : Fin 5) {ends : Nat → Option TState} {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g (correctionScanPc stage)
      (correctionScanFacts p l g stage.val) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hTarget : correctionScanPc stage < target.pc) :
    ∃ next : SchedulerWarpAt l X g (correctionScanPc stage + 4)
      (correctionScanFacts p l g (stage.val + 1)) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  obtain ⟨read, hRead⟩ := cur.consumeShuffleTo hp hX hg .up (fun lane => b32 (part lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) (firstCorrectionFresh stage)
    (firstCorrectionOut hp stage cur)
    hProgress hTarget
  obtain ⟨next, hNextPos⟩ := read.advanceLocalAt (firstCorrectionFoldLocal hp hg stage read)
  exact ⟨next, fun h => hNextPos.symm ▸ hRead h⟩

/-- The five real up-shuffles aggregate the first 31 requests with the sentinel contribution. -/
theorem correctionFirstScanTo {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState} {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 7781 (fun lane =>
      firstCorrectionScanFacts p l (warpLane l g lane)) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hTarget : 7797 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 7801 (correctionScanFacts p l g 5) (shuffles + 5) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s0, h0⟩ : ∃ s0 : SchedulerWarpAt l X g 7781
      (correctionScanFacts p l g 0) shuffles votes ends, s0.pos = cur.pos := by
    apply cur.advanceLocalAt
    intro lane hl
    have ht := cur.checkpoint lane hl
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hReg := ht.2.2.2.2.1
    rw [hLane] at hReg
    refine ⟨_, .refl, ht.mono ⟨?_, ht.2.2.2.2⟩⟩
    change (cur.state lane).regs 7270 = some (b32 (prefixWindow (groupLaneTiles p 0) 1 lane))
    simpa only [prefixWindow_one] using hReg
  have h0' : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g s0.pos src index target := by
    rwa [h0]
  have keep {a b : Nat → Nat} (h : WarpFollowsEvent l X g a src index target →
        WarpFollowsEvent l X g b src index target)
      (ha : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g a src index target) :
      (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g b src index target :=
    ha.elim Or.inl (fun hA => .inr (h hA))
  obtain ⟨s1, h1⟩ := firstCorrectionFold hp hX hg 0 s0 h0'
    (by change 7781 < target.pc; omega)
  obtain ⟨s2, h2⟩ := firstCorrectionFold hp hX hg 1 s1 (keep h1 h0')
    (by change 7785 < target.pc; omega)
  obtain ⟨s3, h3⟩ := firstCorrectionFold hp hX hg 2 s2 (keep h2 (keep h1 h0'))
    (by change 7789 < target.pc; omega)
  obtain ⟨s4, h4⟩ := firstCorrectionFold hp hX hg 3 s3 (keep h3 (keep h2 (keep h1 h0')))
    (by change 7793 < target.pc; omega)
  obtain ⟨s5, h5⟩ := firstCorrectionFold hp hX hg 4 s4 (keep h4 (keep h3 (keep h2 (keep h1 h0'))))
    hTarget
  exact ⟨s5, fun h => h5 (h4 (h3 (h2 (h1 (h0.symm ▸ h)))))⟩

private theorem firstCorrectionFoldMaximal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (correctionScanPc stage)
      (correctionScanFacts p l g stage.val) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (correctionScanPc stage + 4)
      (correctionScanFacts p l g (stage.val + 1)) (shuffles + 1) votes ends) := by
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .up (fun lane => b32 (part lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) (firstCorrectionFresh stage)
    (firstCorrectionOut hp stage cur.toSchedulerWarpAt)
  exact read.advanceLocal (firstCorrectionFoldLocal hp hg stage read.toSchedulerWarpAt)

/-- The five up-shuffles needed for the first correction group all issue in a maximal execution. -/
theorem correctionFirstScanOfMaximal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7781 (fun lane =>
      firstCorrectionScanFacts p l (warpLane l g lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7801 (correctionScanFacts p l g 5)
      (shuffles + 5) votes ends) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s0⟩ := cur.advanceLocal (G := correctionScanFacts p l g 0) (pc' := 7781) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hReg := ht.2.2.2.2.1
    rw [hLane] at hReg
    refine ⟨_, .refl, ht.mono ⟨?_, ht.2.2.2.2⟩⟩
    change (cur.state lane).regs 7270 = some (b32 (prefixWindow (groupLaneTiles p 0) 1 lane))
    simpa only [prefixWindow_one] using hReg)
  obtain ⟨s1⟩ := firstCorrectionFoldMaximal hp hMax hg 0 s0
  obtain ⟨s2⟩ := firstCorrectionFoldMaximal hp hMax hg 1 s1
  obtain ⟨s3⟩ := firstCorrectionFoldMaximal hp hMax hg 2 s2
  obtain ⟨s4⟩ := firstCorrectionFoldMaximal hp hMax hg 3 s3
  exact firstCorrectionFoldMaximal hp hMax hg 4 s4

end
end PTX.Kernels.TmlFa4Fwd.Correction

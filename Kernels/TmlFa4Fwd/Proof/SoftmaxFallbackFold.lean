-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackTiles
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroup
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Lemmas.Flow.WarpScan
import Kernels.TmlFa4Fwd.Flow.Code.Part050

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private def fallbackScanPc (stage : Nat) : Nat := 3192 + 3 * stage

def fallbackScanSrc (stage : Nat) : Nat :=
  if stage = 0 then 7240 else if stage = 5 then 7241 else 2710 + 3 * stage

private def fallbackScanDst (stage : Nat) : Nat := 2711 + 3 * stage

private def fallbackScanGuard (stage lane : Nat) : Bool :=
  if stage = 0 then decide (lane = 0) else decide (2 ^ stage ≤ lane)

def fallbackScanPreds (lane : Nat) : List (Nat × Value) :=
  [(459, .pred (decide (16 ≤ lane))), (460, .pred (decide (8 ≤ lane))),
    (461, .pred (decide (4 ≤ lane))), (462, .pred (decide (2 ≤ lane))),
    (463, .pred (decide (lane = 0)))]

/-- Each of the five guarded shuffles has the same scanned array and retained search frame. -/
def fallbackFoldFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (first cutoff stage : Nat) : List (Nat × Value) :=
  let lane := laneOf l g
  (fallbackScanSrc stage, b32 (prefixWindow (groupLaneTiles p (first + 31)) (2 ^ stage) lane)) ::
    fallbackScanPreds lane ++
    ((7240, b32 (groupLaneTiles p (first + 31) lane)) ::
      fallbackAdvanceFacts p l g warp first cutoff)

private theorem prepareFallbackFold (l : Launch) (g : Nat) {lane : Nat} (hl : lane < 32) :
    Seg kernel [] l g 5 3187 [(1215, b32 lane)] 3192 (fallbackScanPreds lane) := by
  intro t ht
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  have h0 : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  dsimp only [fallbackScanPreds]
  seg_fp ht using
    simp only [compare, Option.getD_some, truncBits_ofNat h32 (by decide),
      toNat_ofNat_lt h64, Value.pred.injEq, decide_eq_decide, h0, h1, h3, h7, h15]
    all_goals omega

/-- Prepare the actual five per-lane select guards without consuming a trace event. -/
theorem warpFallbackFoldStartPreserving {p : Params} {l : Launch} {X : Execution}
    {g first cutoff shuffles votes : Nat} {warp : Fin 8} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3187 (fun lane =>
      (7240, b32 (groupLaneTiles p (first + 31) (laneOf l (warpLane l g lane)))) ::
        fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends) :
    ∃ u : SchedulerWarpAt l X g 3192 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff 0) shuffles votes ends,
      u.pos = cur.pos ∧ u.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let g' := warpLane l g lane
  let ln := laneOf l g'
  let count := groupLaneTiles p (first + 31) ln
  have ht := cur.checkpoint lane hl
  have hLane : ln < 32 := Nat.mod_lt _ (by decide)
  have hAt : At (cur.state lane) 3187 [(1215, b32 ln)] :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl, trivial⟩
  obtain ⟨u, hu, hU⟩ := (prepareFallbackFold l g' hLane).apply hAt
  obtain ⟨hRun, hKeep⟩ := fallbackLinear (by decide) (by decide) ht
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hSource : prefixWindow (groupLaneTiles p (first + 31)) (2 ^ (0 : Nat)) ln = count := by
    simp [prefixWindow_one, count]
  refine ⟨u, run_rtg hRun, hU.mono ?_⟩
  rw [fallbackFoldFacts, fallbackScanSrc, ite_eq_left rfl, hSource]
  change Holds u.regs ((7240, b32 count) ::
    (fallbackScanPreds ln ++ (7240, b32 count) :: fallbackAdvanceFacts p l g' warp first cutoff))
  rw [holds_cons, holds_append]
  exact ⟨hKeep.1, hU.2.2.2.2, hKeep⟩

theorem warpFallbackFoldStart {p : Params} {l : Launch} {X : Execution}
    {g first cutoff shuffles votes : Nat} {warp : Fin 8} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3187 (fun lane =>
      (7240, b32 (groupLaneTiles p (first + 31) (laneOf l (warpLane l g lane)))) ::
        fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends) :
    ∃ u : SchedulerWarpAt l X g 3192 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff 0) shuffles votes ends,
      u.pos = cur.pos := by
  obtain ⟨u, hPos, _⟩ := warpFallbackFoldStartPreserving cur
  exact ⟨u, hPos⟩

private theorem fallbackScanCode (stage : Fin 5) :
    kernel.code[fallbackScanPc stage.val]? = some ⟨none, .warp
      { kind := .shfl .up
        ty := some (.int .b 32)
        dsts := [some (fallbackScanDst stage.val)]
        srcs := [.reg (fallbackScanSrc stage.val), .imm ((2 ^ stage.val : Nat) : Int), .imm 0]
        mask := some (.imm (-1)) }⟩ := by
  fin_cases stage
  · exact Flow.code_3192
  · exact Flow.code_3195
  · exact Flow.code_3198
  · exact Flow.code_3201
  · exact Flow.code_3204

private theorem fallbackScanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (stage : Fin 5) (sum : Nat)
    (hpc : t.pc = fallbackScanPc stage.val) (hf : t.fault = none)
    (hv : t.regs (fallbackScanSrc stage.val) = some (b32 sum)) :
    out kernel Assumptions.all l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (fallbackScanDst stage.val) value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [out_event hf (by rw [hpc]; exact fallbackScanCode stage) rfl rfl]
  change Out.ev (shflTmpl l g t .up (fallbackScanDst stage.val) none
    (.reg (fallbackScanSrc stage.val)) (.imm ((2 ^ stage.val : Nat) : Int))
    (.imm 0) (.imm (-1))) = _
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

private theorem fallbackScanCombine (stage : Fin 5) (l : Launch) (g : Nat) {lane left recv : Nat}
    (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (fallbackScanPc stage.val + 1)
      [(463 - stage.val, .pred (fallbackScanGuard stage.val lane)),
       (fallbackScanSrc stage.val, b32 left), (fallbackScanDst stage.val, b32 recv)]
      (fallbackScanPc (stage.val + 1))
      [(fallbackScanSrc (stage.val + 1),
        b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  by_cases h : 2 ^ stage.val ≤ lane
  · have hGuard : fallbackScanGuard stage.val lane = decide (stage.val ≠ 0) := by
      by_cases hs : stage.val = 0
      · rw [hs, Nat.pow_zero] at h
        simp [fallbackScanGuard, hs, show lane ≠ 0 by omega]
      · simp [fallbackScanGuard, hs, h]
    fin_cases stage <;> dsimp only [fallbackScanPc, fallbackScanSrc, fallbackScanDst] <;>
      intro t ht <;> simp only [hGuard] at ht <;> seg_fp ht using norm_bits [ite_eq_left h]
  · have hGuard : fallbackScanGuard stage.val lane = decide (stage.val = 0) := by
      by_cases hs : stage.val = 0
      · rw [hs, Nat.pow_zero] at h
        simp [fallbackScanGuard, hs, show lane = 0 by omega]
      · simp [fallbackScanGuard, hs, h]
    fin_cases stage <;> dsimp only [fallbackScanPc, fallbackScanSrc, fallbackScanDst] <;>
      intro t ht <;> simp only [hGuard] at ht <;> seg_fp ht using norm_bits [ite_eq_right h]

private theorem fallbackScanFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 2 (fallbackScanPc stage.val + 1)
      [(463 - stage.val, .pred (fallbackScanGuard stage.val lane)),
       (fallbackScanSrc stage.val, b32 (prefixWindow xs (2 ^ stage.val) lane)),
       (fallbackScanDst stage.val,
         b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (fallbackScanPc (stage.val + 1))
      [(fallbackScanSrc (stage.val + 1), b32 (prefixWindow xs (2 ^ (stage.val + 1)) lane))] := by
  rw [Nat.pow_succ', prefixWindow_double]
  have h := fallbackScanCombine stage l g (lane := lane) hsum
  rw [firstScanSource] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

private theorem warpFallbackFoldAfterShuffle {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first cutoff shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hGroup : first + 31 ≤ p.batch) (stage : Fin 5) {ends : Nat → Option TState}
    (read : SchedulerWarpAt l X g (fallbackScanPc stage.val + 1) (fun lane =>
      (fallbackScanDst stage.val,
        b32 (prefixWindow (groupLaneTiles p (first + 31)) (2 ^ stage.val)
          (shflSource .up lane (2 ^ stage.val) 0).1)) ::
        fallbackFoldFacts p l (warpLane l g lane) warp first cutoff stage.val)
      shuffles votes ends) :
    ∃ u : SchedulerWarpAt l X g (fallbackScanPc (stage.val + 1)) (fun lane =>
        fallbackFoldFacts p l (warpLane l g lane) warp first cutoff (stage.val + 1))
        shuffles votes ends, u.pos = read.pos ∧ u.before = read.before := by
  let t := warpLane l g
  let xs := groupLaneTiles p (first + 31)
  let part := prefixWindow xs (2 ^ stage.val)
  let F := fun lane => fallbackScanPreds (laneOf l (t lane)) ++
    ((7240, b32 (xs (laneOf l (t lane)))) :: fallbackAdvanceFacts p l (t lane) warp first cutoff)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  apply read.advanceLocalPreserving
  intro lane hl
  have ht := read.checkpoint lane hl
  have hF : Holds (read.state lane).regs (F lane) := ht.2.2.2.2.2.2
  have hGuard : (read.state lane).regs (463 - stage.val) =
      some (.pred (fallbackScanGuard stage.val lane)) := by
    apply holds_mem hF
    unfold F
    dsimp only [t]
    rw [hLane lane hl]
    fin_cases stage <;> simp [fallbackScanPreds, fallbackScanGuard]
  have htArgs : At (read.state lane) (fallbackScanPc stage.val + 1)
      [(463 - stage.val, .pred (fallbackScanGuard stage.val lane)),
       (fallbackScanSrc stage.val, b32 (part lane)),
       (fallbackScanDst stage.val, b32 (part (shflSource .up lane (2 ^ stage.val) 0).1))] := by
    have h := ht.2.2.2.2.2.1
    change (read.state lane).regs (fallbackScanSrc stage.val) =
      some (b32 (part (laneOf l (warpLane l g lane)))) at h
    rw [hLane lane hl] at h
    exact ht.mono ⟨hGuard, h, ht.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := (fallbackScanFold stage l (t lane) xs
    (groupPrefixOperands_fit hp hGroup hl stage)).apply htArgs
  obtain ⟨hRun, hKeep⟩ := fallbackLinear (F := F lane)
    (by have := stage.isLt; dsimp [fallbackScanPc]; omega)
    (by have := stage.isLt; dsimp [fallbackScanPc]; omega) (ht.mono hF)
    (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl)
    (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl) hu
  have hSum := hU.2.2.2.2.1
  change u.regs (fallbackScanSrc (stage.val + 1)) =
    some (b32 (prefixWindow xs (2 ^ (stage.val + 1)) lane)) at hSum
  refine ⟨u, run_rtg hRun, hU.mono ?_⟩
  change Holds u.regs ((fallbackScanSrc (stage.val + 1),
    b32 (prefixWindow xs (2 ^ (stage.val + 1)) (laneOf l (warpLane l g lane)))) :: F lane)
  exact ⟨by rwa [hLane lane hl], hKeep⟩

private theorem warpFallbackFoldStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first cutoff shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hGroup : first + 31 ≤ p.batch) (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g (fallbackScanPc stage.val) (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff stage.val)
      shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨
      WarpFollowsEvent l X g cur.pos src index target) (hTarget : 3206 < target.pc) :
    ∃ u : SchedulerWarpAt l X g (fallbackScanPc (stage.val + 1)) (fun lane =>
        fallbackFoldFacts p l (warpLane l g lane) warp first cutoff (stage.val + 1))
        (shuffles + 1) votes ends,
      u.pos = (fun lane => cur.pos lane + 1) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g u.pos src index target) := by
  let t := warpLane l g
  let xs := groupLaneTiles p (first + 31)
  let part := prefixWindow xs (2 ^ stage.val)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hFresh : ∀ lane < 32, ∀ x ∈ fallbackFoldFacts p l (t lane) warp first cutoff stage.val,
      x.1 ≠ fallbackScanDst stage.val := by
    intro lane hl
    fin_cases stage <;> exact of_decide_eq_true rfl
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl .up (b32 (part lane)) (2 ^ stage.val) 0
          (fun v _ => next (setReg (cur.state lane) (fallbackScanDst stage.val) v))) := by
    have ht := cur.checkpoint lane hl
    apply fallbackScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1
    have h := ht.2.2.2.2.1
    change (cur.state lane).regs (fallbackScanSrc stage.val) =
      some (b32 (part (laneOf l (warpLane l g lane)))) at h
    rwa [hLane lane hl] at h
  obtain ⟨read, hPos, _, hRead⟩ :=
    cur.consumeShuffleToRecorded hp hX hg .up (fun lane => b32 (part lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) hFresh hOut hProgress
    (by have := stage.isLt; dsimp [fallbackScanPc]; omega)
  obtain ⟨u, hu, _⟩ := warpFallbackFoldAfterShuffle hp hg hGroup stage read
  exact ⟨u, hu.trans hPos, fun h => hu.symm ▸ hRead h⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g first cutoff shuffles votes : Nat}
    {warp : Fin 8} (hg : g < l.threads) (hGroup : first + 31 ≤ p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3192 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff 0) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
include hp hX hg hGroup cur hProgress

/-- Replay the five up shuffles in the actual fallback group and compute its inclusive prefix. -/
theorem warpFallbackFoldRecorded (hTarget : 3206 < target.pc) :
    ∃ u : SchedulerWarpAt l X g 3207 (fun lane =>
        fallbackFoldFacts p l (warpLane l g lane) warp first cutoff 5)
        (shuffles + 5) votes ends,
      u.pos = (fun lane => cur.pos lane + 5) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g u.pos src index target) := by
  obtain ⟨s1, hPos1, h1⟩ := warpFallbackFoldStep hp hX hg hGroup 0 cur hProgress hTarget
  obtain ⟨s2, hPos2, h2⟩ := warpFallbackFoldStep hp hX hg hGroup 1 s1
    (hProgress.imp_right h1) hTarget
  obtain ⟨s3, hPos3, h3⟩ := warpFallbackFoldStep hp hX hg hGroup 2 s2
    (hProgress.imp_right (h2 ∘ h1)) hTarget
  obtain ⟨s4, hPos4, h4⟩ := warpFallbackFoldStep hp hX hg hGroup 3 s3
    (hProgress.imp_right (h3 ∘ h2 ∘ h1)) hTarget
  obtain ⟨s5, hPos5, h5⟩ := warpFallbackFoldStep hp hX hg hGroup 4 s4
    (hProgress.imp_right (h4 ∘ h3 ∘ h2 ∘ h1)) hTarget
  refine ⟨s5, ?_, h5 ∘ h4 ∘ h3 ∘ h2 ∘ h1⟩
  rw [hPos5, hPos4, hPos3, hPos2, hPos1]

theorem warpFallbackFold (hTarget : 3206 < target.pc) :
    ∃ u : SchedulerWarpAt l X g 3207 (fun lane =>
        fallbackFoldFacts p l (warpLane l g lane) warp first cutoff 5)
        (shuffles + 5) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g u.pos src index target := by
  obtain ⟨u, _, hFollow⟩ := warpFallbackFoldRecorded hp hX hg hGroup cur hProgress hTarget
  exact ⟨u, hFollow⟩
end

private theorem warpFallbackFoldStepOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first cutoff shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hGroup : first + 31 ≤ p.batch) (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (fallbackScanPc stage.val) (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff stage.val)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (fallbackScanPc (stage.val + 1)) (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff (stage.val + 1))
      (shuffles + 1) votes ends) := by
  let t := warpLane l g
  let xs := groupLaneTiles p (first + 31)
  let part := prefixWindow xs (2 ^ stage.val)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hFresh : ∀ lane < 32, ∀ x ∈ fallbackFoldFacts p l (t lane) warp first cutoff stage.val,
      x.1 ≠ fallbackScanDst stage.val := by
    intro lane hl
    fin_cases stage <;> exact of_decide_eq_true rfl
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl .up (b32 (part lane)) (2 ^ stage.val) 0
          (fun v _ => next (setReg (cur.state lane) (fallbackScanDst stage.val) v))) := by
    have ht := cur.checkpoint lane hl
    apply fallbackScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1
    have h := ht.2.2.2.2.1
    change (cur.state lane).regs (fallbackScanSrc stage.val) =
      some (b32 (part (laneOf l (warpLane l g lane)))) at h
    rwa [hLane lane hl] at h
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .up (fun lane => b32 (part lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) hFresh hOut
  obtain ⟨next, hPos, hState⟩ :=
    warpFallbackFoldAfterShuffle hp hg hGroup stage read.toSchedulerWarpAt
  exact ⟨read.reframe next hPos hState⟩

/-- Perform the five real scans of a reached fallback group in a maximal execution. -/
theorem warpFallbackFoldOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first cutoff shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hGroup : first + 31 ≤ p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3192 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff 0) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3207 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first cutoff 5)
      (shuffles + 5) votes ends) := by
  have steps (stage : Nat) (hStage : stage ≤ 5) :
      Nonempty (SchedulerWarpReached l X g (fallbackScanPc stage) (fun lane =>
        fallbackFoldFacts p l (warpLane l g lane) warp first cutoff stage)
        (shuffles + stage) votes ends) := by
    induction stage with
    | zero => exact ⟨cur⟩
    | succ stage ih =>
      have hLt : stage < 5 := by omega
      obtain ⟨reached⟩ := ih hLt.le
      exact warpFallbackFoldStepOfMaximal hp hMax hg hGroup ⟨stage, hLt⟩ reached
  exact steps 5 le_rfl


end
end PTX.Kernels.TmlFa4Fwd.Softmax

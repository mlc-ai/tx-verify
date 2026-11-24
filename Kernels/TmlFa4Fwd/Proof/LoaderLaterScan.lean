-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderLaterTiles

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def laterScanPc (stage : Fin 5) : Nat := 268 + 3 * stage.val

def laterScanSrc (stage : Fin 5) : Nat :=
  if stage.val = 0 then 7162 else 1734 + 3 * stage.val

def laterScanDst (stage : Fin 5) : Nat := 1735 + 3 * stage.val

def laterScanResult (stage : Fin 5) : Nat :=
  if stage.val = 4 then 7163 else 1737 + 3 * stage.val

def laterScanGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2 ^ stage.val ≤ lane)

/-- Prepare the five guards for the up-shuffles that follow a group reload. -/
theorem laterScanPredicates (l : Launch) (g : Nat) {lane count : Nat} (hl : lane < 32) :
    Seg kernel [] l g 5 263 [(1073, b32 lane), (7162, b32 count)] 268
      [(82, .pred (decide (16 ≤ lane))), (83, .pred (decide (8 ≤ lane))),
       (84, .pred (decide (4 ≤ lane))), (85, .pred (decide (2 ≤ lane))),
       (86, .pred (decide (lane = 0))), (7162, b32 count)] := by
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

theorem laterScanInstr (stage : Fin 5) :
    kernel.code[laterScanPc stage]? = some ⟨none, .warp
      { kind := .shfl .up
        ty := some (.int .b 32)
        dsts := [some (laterScanDst stage)]
        srcs := [.reg (laterScanSrc stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0]
        mask := some (.imm (-1)) }⟩ := by
  fin_cases stage
  · exact Flow.code_268
  · exact Flow.code_271
  · exact Flow.code_274
  · exact Flow.code_277
  · exact Flow.code_280

variable {p : Params} {l : Launch}

theorem laterScanTemplate {m : Mem0} (hp : Pre p l m) (g : Nat) (t : TState) (stage : Fin 5)
    (sum : Nat) (hpc : t.pc = laterScanPc stage) (hf : t.fault = none)
    (hv : t.regs (laterScanSrc stage) = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (laterScanDst stage) value))) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  rw [out_event hf (by rw [hpc]; exact laterScanInstr stage) rfl rfl]
  change Out.ev (shflTmpl l g t .up (laterScanDst stage) none (.reg (laterScanSrc stage))
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

theorem laterScanCombine (stage : Fin 5) (l : Launch) (g : Nat) {lane left recv : Nat}
    (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (laterScanPc stage + 1)
      [(86 - stage.val, .pred (laterScanGuard stage lane)),
       (laterScanSrc stage, b32 left), (laterScanDst stage, b32 recv)]
      (laterScanPc stage + 3)
      [(laterScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  by_cases h : 2 ^ stage.val ≤ lane
  · have hGuard : laterScanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hs : stage.val = 0
      · rw [hs, Nat.pow_zero] at h
        simp [laterScanGuard, hs, show lane ≠ 0 by omega]
      · simp [laterScanGuard, hs, h]
    fin_cases stage <;> intro t ht <;>
      simp only [hGuard] at ht <;> seg_fp ht using norm_bits [ite_eq_left h]
  · have hGuard : laterScanGuard stage lane = decide (stage.val = 0) := by
      by_cases hs : stage.val = 0
      · rw [hs, Nat.pow_zero] at h
        simp [laterScanGuard, hs, show lane = 0 by omega]
      · simp [laterScanGuard, hs, h]
    fin_cases stage <;> intro t ht <;>
      simp only [hGuard] at ht <;> seg_fp ht using norm_bits [ite_eq_right h]

theorem laterScanFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 2 (laterScanPc stage + 1)
      [(86 - stage.val, .pred (laterScanGuard stage lane)),
       (laterScanSrc stage, b32 (prefixWindow xs (2 ^ stage.val) lane)),
       (laterScanDst stage,
         b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (laterScanPc stage + 3)
      [(laterScanResult stage, b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := laterScanCombine stage l g (lane := lane) hsum
  rw [firstScanSource] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

/-- Values that are not written by any round of the later scan. -/
def laterScanCarry (p : Params) (l : Launch) (g warp first lane : Nat) : List (Nat × Value) :=
  [(82, .pred (decide (16 ≤ lane))), (83, .pred (decide (8 ≤ lane))),
   (84, .pred (decide (4 ≤ lane))), (85, .pred (decide (2 ≤ lane))),
   (86, .pred (decide (lane = 0)))] ++ laterTilesFacts p l (warpLane l g lane) warp first

/-- The input register varies by round; the guarded loop uses the same other inputs. -/
def laterScanFacts (p : Params) (l : Launch) (g warp first stage lane : Nat) : List (Nat × Value) :=
  (if h : stage < 5 then laterScanSrc ⟨stage, h⟩ else 7163,
    b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage) lane)) ::
  laterScanCarry p l g warp first lane

private theorem laterScanFresh {g warp first lane : Nat} (stage : Fin 5) {pair : Nat × Value}
    (hm : pair ∈ laterScanFacts p l g warp first stage.val lane) :
    pair.1 ≠ laterScanDst stage := by
  have hm' := List.mem_map_of_mem (f := Prod.fst) hm
  intro he
  rw [he] at hm'
  have hDisjoint :
      laterScanDst stage ∉ (laterScanFacts p l g warp first stage.val lane).map Prod.fst := by
    fin_cases stage <;> exact of_decide_eq_true rfl
  exact hDisjoint hm'

private theorem laterScanOut {m : Mem0} (hp : Pre p l m) {g warp first lane : Nat} (stage : Fin 5)
    {t : TState} (ht : At t (laterScanPc stage) (laterScanFacts p l g warp first stage.val lane)) :
    out kernel Assumptions.all l (warpLane l g lane) t =
      .ev (.shfl .up (b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))
        (2 ^ stage.val) 0 (fun v _ => next (setReg t (laterScanDst stage) v))) := by
  let part := prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
  have hReg : (t).regs (laterScanSrc stage) = some (b32 (part lane)) := by
    have h := ht.2.2.2.2
    unfold laterScanFacts at h
    simp only [dite_eq_left stage.isLt] at h
    exact h.1
  rw [loaderOutCore (by rw [ht.1]; have := stage.isLt; simp [laterScanPc]; omega)
    (by rw [ht.1]; have := stage.isLt; simp [laterScanPc]; omega)]
  exact laterScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1 hReg

private theorem laterScanFoldLocal {m : Mem0} (hp : Pre p l m) {g warp first lane : Nat}
    (hf : first ≤ p.batch) (stage : Fin 5) (hl : lane < 32) {t : TState}
    (hAt : At t (laterScanPc stage + 1)
      ((laterScanDst stage, b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
        (shflSource .up lane (2 ^ stage.val) 0).1)) ::
        laterScanFacts p l g warp first stage.val lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u (laterScanPc stage + 3) (laterScanFacts p l g warp first (stage.val + 1) lane) := by
  let part := prefixWindow (groupLaneTiles p first) (2 ^ stage.val)
  let thread := warpLane l g lane
  let regs := (laterScanCarry p l g warp first lane).map Prod.fst
  have hReads := hAt.2.2.2.2.2
  unfold laterScanFacts at hReads
  simp only [dite_eq_left stage.isLt] at hReads
  have hCarry : Holds (t).regs (laterScanCarry p l g warp first lane) := hReads.2
  have hReg : (t).regs (86 - stage.val) =
      some (.pred (laterScanGuard stage lane)) := by
    apply holds_mem hCarry
    fin_cases stage <;> simp [laterScanCarry, laterScanGuard]
  have hFoldAt : At (t) (laterScanPc stage + 1)
      [(86 - stage.val, .pred (laterScanGuard stage lane)),
       (laterScanSrc stage, b32 (part lane)),
       (laterScanDst stage, b32 (part (shflSource .up lane (2 ^ stage.val) 0).1))] :=
    hAt.mono ⟨hReg, hReads.1, hAt.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := laterScanFold stage l thread _ (groupPrefixOperands_fit hp hf hl stage)
    _ hFoldAt
  obtain ⟨huA, hFrame⟩ := loaderLinear (regs := regs)
    (by have := stage.isLt; simp [laterScanPc]; omega)
    (by have := stage.isLt; simp [laterScanPc]; omega) hFoldAt.1
    (by fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
  have hSaved := holdsSchedulerFrame hCarry hFrame (fun _ h => List.mem_map_of_mem h)
  have hNextReg : (if h : stage.val + 1 < 5 then laterScanSrc ⟨stage.val + 1, h⟩ else 7163) =
      laterScanResult stage := by
    fin_cases stage <;> rfl
  have hNextWidth : 2 ^ (stage.val + 1) = 2 * 2 ^ stage.val := by
    rw [Nat.pow_succ, Nat.mul_comm]
  refine ⟨u, run_rtg huA, hU.mono ?_⟩
  unfold laterScanFacts
  rw [hNextReg, hNextWidth]
  exact ⟨hU.2.2.2.2.1, hSaved⟩

private theorem laterScanSetup {m : Mem0} (hp : Pre p l m) {g warp first lane : Nat}
    (hg : g < l.threads) (hf : first < p.batch) (hl : lane < 32) {t : TState}
    (ht : At t 248
      ((1728, b32 (drainCuQ p (first + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u 268 (laterScanFacts p l g warp first 0 lane) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  let thread := warpLane l g lane
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane hBlock hg hl).2
  obtain ⟨_, u, hu, hU⟩ := loaderLaterTiles hp (g := thread) (t := t) hf
    (by simpa only [hLane] using ht)
  let keep := (laterTilesFacts p l thread warp first).map Prod.fst
  have hCount := hU.2.2.2.2.1
  rw [hLane] at hCount
  have hWord : u.regs 1073 = some (b32 lane) := by
    have h := holds_lookup hU.2.2.2.2
      (show (laterTilesFacts p l thread warp first).lookup 1073 =
        some (b32 (laneOf l thread)) from rfl)
    rw [hLane] at h
    exact h
  have hAt : At u 263 [(1073, b32 lane), (7162, b32 (groupLaneTiles p first lane))] :=
    hU.mono ⟨hWord, hCount, trivial⟩
  obtain ⟨v, hv, hV⟩ := laterScanPredicates l thread hl u hAt
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) hU.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hPreserved := holdsSchedulerFrame hU.2.2.2.2 hvFrame (fun _ h => List.mem_map_of_mem h)
  have hSave : Holds v.regs (laterScanCarry p l g warp first lane) :=
    ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.1,
      hV.2.2.2.2.2.2.2.2.1, hPreserved⟩
  refine ⟨v, run_rtg (run_comp hu hvA), hV.mono ⟨?_, hSave⟩⟩
  change v.regs 7162 = some (b32 (prefixWindow (groupLaneTiles p first) 1 lane))
  simpa only [prefixWindow_one] using hV.2.2.2.2.2.2.2.2.2.1

private theorem laterScanStageTo {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first ≤ p.batch) (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g (laterScanPc stage)
      (laterScanFacts p l g warp first stage.val) shuffles votes ends) {src index : Nat}
    {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : laterScanPc stage < target.pc) :
    ∃ next : SchedulerWarpAt l X g (laterScanPc stage + 3)
      (laterScanFacts p l g warp first (stage.val + 1)) (shuffles + 1) votes ends,
      next.pos = (fun lane => cur.pos lane + 1) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target) := by
  obtain ⟨read, hRead, _, hAdvance⟩ := cur.consumeShuffleToRecorded hp hX hg .up
    (fun lane => b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) (fun _ _ _ => laterScanFresh stage)
    (fun lane hl => laterScanOut hp stage (cur.checkpoint lane hl)) hProgress hPc
  obtain ⟨result, hPos⟩ := read.advanceLocalAt (pc' := laterScanPc stage + 3)
    (G := laterScanFacts p l g warp first (stage.val + 1))
    (fun lane hl => laterScanFoldLocal hp hf stage hl (read.checkpoint lane hl))
  exact ⟨result, hPos.trans hRead, fun h => hPos.symm ▸ hAdvance h⟩

section
variable {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp first shuffles votes : Nat} (hg : g < l.threads) (hf : first < p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 248 (fun lane =>
      (1728, b32 (drainCuQ p (first + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp first) shuffles votes ends) {src index : Nat}
    {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
include hp hX hg hf cur hProgress

/-- Replay the five actual fallback up-shuffles and the decoded prefix arithmetic. -/
theorem loaderLaterScanWithLength (hPc : 280 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 283
      (laterScanFacts p l g warp first 5) (shuffles + 5) votes ends,
      next.pos = (fun lane => cur.pos lane + 5) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target) := by
  obtain ⟨s0, hPos⟩ := cur.advanceLocalAt (pc' := 268)
    (G := laterScanFacts p l g warp first 0)
    (fun lane hl => laterScanSetup hp hg hf hl (cur.checkpoint lane hl))
  have h0 : WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g s0.pos src index target := fun h => hPos.symm ▸ h
  obtain ⟨s1, hPos1, h1⟩ := laterScanStageTo hp hX hg hf.le 0 s0 (hProgress.imp_right h0) (by
    change 268 < target.pc; omega)
  obtain ⟨s2, hPos2, h2⟩ := laterScanStageTo hp hX hg hf.le 1 s1 (hProgress.imp_right (h1 ∘ h0)) (by
    change 271 < target.pc; omega)
  obtain ⟨s3, hPos3, h3⟩ := laterScanStageTo hp hX hg hf.le 2 s2
    (hProgress.imp_right (h2 ∘ h1 ∘ h0)) (by
    change 274 < target.pc; omega)
  obtain ⟨s4, hPos4, h4⟩ := laterScanStageTo hp hX hg hf.le 3 s3
    (hProgress.imp_right (h3 ∘ h2 ∘ h1 ∘ h0)) (by change 277 < target.pc; omega)
  obtain ⟨s5, hPos5, h5⟩ := laterScanStageTo hp hX hg hf.le 4 s4
    (hProgress.imp_right (h4 ∘ h3 ∘ h2 ∘ h1 ∘ h0)) hPc
  refine ⟨s5,?_,h5 ∘ h4 ∘ h3 ∘ h2 ∘ h1 ∘ h0⟩
  rw [hPos5,hPos4,hPos3,hPos2,hPos1,hPos]

theorem loaderLaterScanTo (hPc : 280 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 283
      (laterScanFacts p l g warp first 5) (shuffles + 5) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  obtain ⟨next,_,hAdvance⟩ := loaderLaterScanWithLength hp hX hg hf cur hProgress hPc
  exact ⟨next,hAdvance⟩
end

private theorem laterScanStageOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first ≤ p.batch) (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (laterScanPc stage)
      (laterScanFacts p l g warp first stage.val) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (laterScanPc stage + 3)
      (laterScanFacts p l g warp first (stage.val + 1)) (shuffles + 1) votes ends) := by
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .up
    (fun lane => b32 (prefixWindow (groupLaneTiles p first) (2 ^ stage.val) lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) (fun _ _ _ => laterScanFresh stage)
    (fun lane hl => laterScanOut hp stage (cur.checkpoint lane hl))
  exact read.advanceLocal
    (fun lane hl => laterScanFoldLocal hp hf stage hl (read.checkpoint lane hl))

/-- Replay the fallback prefix scan at the actual frontier of a maximal execution. -/
theorem loaderLaterScanOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 248 (fun lane =>
      (1728, b32 (drainCuQ p (first + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 283
      (laterScanFacts p l g warp first 5) (shuffles + 5) votes ends) := by
  obtain ⟨s0⟩ := cur.advanceLocal (pc' := 268) (G := laterScanFacts p l g warp first 0)
    (fun lane hl => laterScanSetup hp hg hf hl (cur.checkpoint lane hl))
  obtain ⟨s1⟩ := laterScanStageOfMaximal hp hMax hg hf.le 0 s0
  obtain ⟨s2⟩ := laterScanStageOfMaximal hp hMax hg hf.le 1 s1
  obtain ⟨s3⟩ := laterScanStageOfMaximal hp hMax hg hf.le 2 s2
  obtain ⟨s4⟩ := laterScanStageOfMaximal hp hMax hg hf.le 3 s3
  exact laterScanStageOfMaximal hp hMax hg hf.le 4 s4

/-- The same fallback scan in a terminated execution. -/
theorem loaderLaterScan {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first shuffles votes : Nat}
    (hg : g < l.threads) (hf : first < p.batch)
    (cur : SchedulerWarpAt l X g 248 (fun lane =>
      (1728, b32 (drainCuQ p (first + (shflSource .down lane 1 31).1))) ::
        laterReadFacts p l (warpLane l g lane) warp first) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 283
      (laterScanFacts p l g warp first 5) (shuffles + 5) votes) := by
  obtain ⟨next, _⟩ := loaderLaterScanTo hp hX hg hf cur (src := 0) (index := 0)
    (target := ⟨281, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨next⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderFirstTiles
public import Kernels.TmlFa4Fwd.Proof.LoaderStartupTrace
public import Kernels.TmlFa4Fwd.Proof.ResultGeometry
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroup
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem scanSignedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

def loaderScanPc (stage : Fin 5) : Nat := 206 + 4 * stage.val

def loaderScanSrc : Fin 5 → Nat
  | 0 => 7162
  | 1 => 1716
  | 2 => 1719
  | 3 => 1722
  | 4 => 1725

def loaderScanDst (stage : Fin 5) : Nat := 1714 + 3 * stage.val

def loaderScanResult (stage : Fin 5) : Nat :=
  if stage.val = 4 then 7163 else 1716 + 3 * stage.val

theorem loaderScanCode (stage : Fin 5) :
    kernel.code[loaderScanPc stage]? = some ⟨none, .warp
      { kind := .shfl .up
        ty := some (.int .b 32)
        dsts := [some (loaderScanDst stage)]
        srcs := [.reg (loaderScanSrc stage), .imm ((2 ^ stage.val : Nat) : Int), .imm 0]
        mask := some (.imm (-1)) }⟩ := by
  fin_cases stage
  · exact Flow.code_206
  · exact Flow.code_210
  · exact Flow.code_214
  · exact Flow.code_218
  · exact Flow.code_222

/-- Each of the first pass's five scan rounds shuffles the previous partial sum by the exact
doubling offset. -/
theorem loaderScanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (stage : Fin 5) (sum : Nat)
    (hpc : t.pc = loaderScanPc stage) (hf : t.fault = none)
    (hv : t.regs (loaderScanSrc stage) = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .up (b32 sum) (2 ^ stage.val) 0
      (fun value _ => next (setReg t (loaderScanDst stage) value))) := by
  have hb : l.block % 32 = 0 := by rw [hp.block]
  have hc := loaderScanCode stage
  rw [← hpc] at hc
  rw [out_event hf hc rfl rfl]
  change Out.ev (shflTmpl l g t .up (loaderScanDst stage) none (.reg (loaderScanSrc stage))
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

private def loaderScanGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2 ^ stage.val ≤ lane)

private theorem loaderScanCompare (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) :
    Seg kernel [] l g 1 (loaderScanPc stage + 1)
      [(1073, b32 lane), (loaderScanSrc stage, b32 left), (loaderScanDst stage, b32 recv)]
      (loaderScanPc stage + 2)
      [(68 + stage.val, .pred (loaderScanGuard stage lane)),
       (loaderScanSrc stage, b32 left), (loaderScanDst stage, b32 recv)] := by
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
      simp only [loaderScanGuard, Nat.reduceEqDiff, ↓reduceIte, compare, Option.getD_some,
        truncBits_ofNat hLane (by decide), toNat_ofNat_lt hLane64,
        Value.pred.injEq, decide_eq_decide, hz, h1, h3, h7, h15]
      all_goals omega

private theorem loaderScanSelect (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 2 (loaderScanPc stage + 2)
      [(68 + stage.val, .pred (loaderScanGuard stage lane)),
       (loaderScanSrc stage, b32 left), (loaderScanDst stage, b32 recv)]
      (loaderScanPc stage + 4)
      [(loaderScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] := by
  have hLeft : left < 2 ^ 32 := by omega
  have hRecv : recv < 2 ^ 32 := by omega
  by_cases h : 2 ^ stage.val ≤ lane
  · have hp : loaderScanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [loaderScanGuard, hst, show lane ≠ 0 by omega]
      · simp [loaderScanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_left h]
  · have hp : loaderScanGuard stage lane = decide (stage.val = 0) := by
      by_cases hst : stage.val = 0
      · rw [hst, Nat.pow_zero] at h
        simp [loaderScanGuard, hst, show lane = 0 by omega]
      · simp [loaderScanGuard, h, hst]
    fin_cases stage <;> intro t ht <;>
      simp only [hp] at ht <;>
      seg_fp ht using norm_bits [ite_eq_right h]

/-- The three local instructions after an up-shuffle implement its guarded addition. -/
theorem loaderScanCombine (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat} (hl : lane < 32) (hsum : left + recv < 2 ^ 32) :
    Seg kernel [] l g 3 (loaderScanPc stage + 1)
      [(1073, b32 lane), (loaderScanSrc stage, b32 left), (loaderScanDst stage, b32 recv)]
      (loaderScanPc stage + 4)
      [(loaderScanResult stage, b32 (left + if 2 ^ stage.val ≤ lane then recv else 0))] :=
  (loaderScanCompare stage l g hl).comp (loaderScanSelect stage l g hl hsum)

/-- The shuffle source given by PTX and the decoded local addition implement one round of the
inclusive prefix scan. -/
theorem loaderScanFold (stage : Fin 5) (l : Launch) (g : Nat) (xs : Nat → Nat)
    {lane : Nat} (hl : lane < 32)
    (hsum : prefixWindow xs (2 ^ stage.val) lane +
      prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1 < 2 ^ 32) :
    Seg kernel [] l g 3 (loaderScanPc stage + 1)
      [(1073, b32 lane), (loaderScanSrc stage, b32 (prefixWindow xs (2 ^ stage.val) lane)),
       (loaderScanDst stage,
         b32 (prefixWindow xs (2 ^ stage.val) (shflSource .up lane (2 ^ stage.val) 0).1))]
      (loaderScanPc stage + 4)
      [(loaderScanResult stage, b32 (prefixWindow xs (2 * 2 ^ stage.val) lane))] := by
  rw [prefixWindow_double]
  have h := loaderScanCombine stage l g hl hsum
  rw [Epilogue.firstScanSource] at h ⊢
  by_cases hcut : 2 ^ stage.val ≤ lane <;> simpa only [hcut, ↓reduceIte] using h

def loaderScanFacts (p : Params) (l : Launch) (g warp stage lane : Nat) :
    List (Nat × Value) :=
  (if h : stage < 5 then loaderScanSrc ⟨stage, h⟩ else 7163,
    b32 (prefixWindow (groupLaneTiles p 0) (2 ^ stage) lane)) ::
  firstLoaderScanFacts p l (warpLane l g lane) warp

/-- The up-shuffle's output register is outside the scan input frame. -/
theorem loaderScanDstFresh {p : Params} {l : Launch} {g warp lane : Nat} (stage : Fin 5)
    {pair : Nat × Value} (hm : pair ∈ loaderScanFacts p l g warp stage.val lane) :
    pair.1 ≠ loaderScanDst stage := by
  have hm' := List.mem_map_of_mem (f := Prod.fst) hm
  intro he
  rw [he] at hm'
  have hDisjoint :
      loaderScanDst stage ∉ (loaderScanFacts p l g warp stage.val lane).map Prod.fst := by
    fin_cases stage <;> exact of_decide_eq_true rfl
  exact hDisjoint hm'

/-- The next up-shuffle reads the checked partial prefix of the issuing lane. -/
theorem loaderFirstScanOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp lane : Nat} (stage : Fin 5) {t : TState}
    (ht : At t (loaderScanPc stage) (loaderScanFacts p l g warp stage.val lane)) :
    out kernel Assumptions.all l (warpLane l g lane) t =
      .ev (.shfl .up (b32 (prefixWindow (groupLaneTiles p 0) (2 ^ stage.val) lane))
        (2 ^ stage.val) 0 (fun v _ => next (setReg t (loaderScanDst stage) v))) := by
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  have hreg : t.regs (loaderScanSrc stage) = some (b32 (part lane)) := by
    have hMem := ht.2.2.2.2
    unfold loaderScanFacts at hMem
    simp only [dite_eq_left stage.isLt] at hMem
    exact hMem.1
  rw [loaderOutCore (by rw [ht.1]; have := stage.isLt; simp [loaderScanPc]; omega)
    (by rw [ht.1]; have := stage.isLt; simp [loaderScanPc]; omega)]
  exact loaderScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1 hreg

/-- Continue from one actual predecessor shuffle through the decoded local scan fold. -/
theorem loaderFirstScanFoldLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp lane : Nat} (stage : Fin 5) (hl : lane < 32)
    (hLane : laneOf l (warpLane l g lane) = lane) {t : TState}
    (hAt : At t (loaderScanPc stage + 1)
      ((loaderScanDst stage, b32 (prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
        (shflSource .up lane (2 ^ stage.val) 0).1)) :: loaderScanFacts p l g warp stage.val lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u (loaderScanPc stage + 4) (loaderScanFacts p l g warp (stage.val + 1) lane) := by
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  let thread := warpLane l g lane
  let regs := (firstLoaderScanFacts p l thread warp).map Prod.fst
  have hCarry : Holds t.regs (firstLoaderScanFacts p l thread warp) := by
    have h := hAt.2.2.2.2.2
    unfold loaderScanFacts at h
    simp only [dite_eq_left stage.isLt] at h
    exact h.2
  have hReg : t.regs 1073 = some (b32 lane) := by
    have h := holds_mem hCarry (by simp [firstLoaderScanFacts, loaderCuQFacts] :
      (1073, b32 (laneOf l thread)) ∈ firstLoaderScanFacts p l thread warp)
    change laneOf l thread = lane at hLane
    rw [hLane] at h
    exact h
  have hFoldAt : At t (loaderScanPc stage + 1)
      [(1073, b32 lane), (loaderScanSrc stage, b32 (part lane)),
       (loaderScanDst stage, b32 (part (shflSource .up lane (2 ^ stage.val) 0).1))] := by
    have h := hAt.2.2.2.2.2
    unfold loaderScanFacts at h
    simp only [dite_eq_left stage.isLt] at h
    exact hAt.mono ⟨hReg, h.1, hAt.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := loaderScanFold stage l thread _ hl
    (groupPrefixOperands_fit hp (Nat.zero_le p.batch) hl stage) _ hFoldAt
  obtain ⟨huA, hFrame⟩ := loaderLinear (regs := regs)
    (by have := stage.isLt; simp [loaderScanPc]; omega)
    (by have := stage.isLt; simp [loaderScanPc]; omega) hFoldAt.1
    (by fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
  have hSaved := holdsSchedulerFrame hCarry hFrame (fun _ h => List.mem_map_of_mem h)
  have hNextReg : (if h : stage.val + 1 < 5 then
      loaderScanSrc ⟨stage.val + 1, h⟩ else 7163) = loaderScanResult stage := by
    fin_cases stage <;> rfl
  have hNextWidth : 2 ^ (stage.val + 1) = 2 * 2 ^ stage.val := by
    rw [Nat.pow_succ, Nat.mul_comm]
  refine ⟨u, run_rtg huA, hU.mono ?_⟩
  unfold loaderScanFacts
  rw [hNextReg, hNextWidth]
  exact ⟨hU.2.2.2.2.1, hSaved⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem firstLoaderFoldTo (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp shuffles votes : Nat} (hg : g < l.threads) (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g (loaderScanPc stage)
      (loaderScanFacts p l g warp stage.val) shuffles votes ends) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : loaderScanPc stage < target.pc) :
    ∃ result : SchedulerWarpAt l X g (loaderScanPc stage + 4)
      (loaderScanFacts p l g warp (stage.val + 1)) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨read,hAdvance⟩ := cur.consumeShuffleTo hp hX hg .up (fun lane => b32 (part lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) (fun _ _ _ => loaderScanDstFresh stage)
    (fun lane hl => loaderFirstScanOut hp stage (cur.checkpoint lane hl)) hProgress hPc
  obtain ⟨result,hPos⟩ := read.advanceLocalAt
    (fun lane hl => loaderFirstScanFoldLocal hp stage hl (Step.sameWarp_lane hBlock hg hl).2
      (read.checkpoint lane hl))
  exact ⟨result, fun h => hPos.symm ▸ hAdvance h⟩

/-- The five real up-shuffles aggregate the first 31 requests with the sentinel contribution. -/
theorem loaderFirstScanTo (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 206 (fun lane =>
      firstLoaderScanFacts p l (warpLane l g lane) warp) shuffles votes ends) {src index : Nat}
    {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 222 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 226 (loaderScanFacts p l g warp 5) (shuffles + 5) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s0, hPos⟩ := cur.advanceLocalAt (G := loaderScanFacts p l g warp 0) (pc' := 206) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hReg := ht.2.2.2.2.1
    rw [hLane] at hReg
    refine ⟨_, .refl, ht.mono ⟨?_, ht.2.2.2.2⟩⟩
    change (cur.state lane).regs 7162 = some (b32 (prefixWindow (groupLaneTiles p 0) 1 lane))
    simpa only [prefixWindow_one] using hReg)
  have h0 : WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g s0.pos src index target := fun h => hPos.symm ▸ h
  obtain ⟨s1, h1⟩ := firstLoaderFoldTo hp hX hg 0 s0 (hProgress.imp_right h0) (by
    change 206 < target.pc; omega)
  obtain ⟨s2, h2⟩ := firstLoaderFoldTo hp hX hg 1 s1 (hProgress.imp_right (h1 ∘ h0)) (by
    change 210 < target.pc; omega)
  obtain ⟨s3, h3⟩ := firstLoaderFoldTo hp hX hg 2 s2 (hProgress.imp_right (h2 ∘ h1 ∘ h0)) (by
    change 214 < target.pc; omega)
  obtain ⟨s4, h4⟩ := firstLoaderFoldTo hp hX hg 3 s3
    (hProgress.imp_right (h3 ∘ h2 ∘ h1 ∘ h0)) (by change 218 < target.pc; omega)
  obtain ⟨s5, h5⟩ := firstLoaderFoldTo hp hX hg 4 s4
    (hProgress.imp_right (h4 ∘ h3 ∘ h2 ∘ h1 ∘ h0)) hPc
  exact ⟨s5, h5 ∘ h4 ∘ h3 ∘ h2 ∘ h1 ∘ h0⟩

theorem loaderFirstTotalTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (sum : Nat)
    (hpc : t.pc = 226) (hf : t.fault = none) (hv : t.regs 7163 = some (b32 sum)) :
    out kernel [] l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7164 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_226) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7164 none (.reg 7163) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

/-- The first group's tile total is multiplied by the number of heads before comparing it to
the CTA index. -/
theorem loaderFirstLimit (l : Launch) (g : Nat) {count heads cta : Nat}
    (hc : count < 2 ^ 31) (hh : heads < 2 ^ 31) (hg : cta < 2 ^ 31)
    (htotal : count * heads < 2 ^ 31) :
    Seg kernel [] l g 3 227 [(7164, b32 count), (7136, b32 heads), (1072, b32 cta)] 230
      [(7166, b32 (count * heads)), (73, .pred (decide (cta < count * heads))),
       (7165, b32 0)] := by
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
        truncBits_ofNat hTotal (by decide), compare, Option.getD_some, scanSignedWord hg,
        scanSignedWord htotal, Int.ofNat_lt]

/-- The first group's total and lane prefix are preserved across its scheduler branch. -/
def loaderFirstRouteFacts (p : Params) (l : Launch) (g warp lane : Nat) :
    List (Nat × Value) :=
  [(7166, b32 (tilePrefix p (min p.batch 31) * p.heads)), (7165, b32 0),
    (7164, b32 (tilePrefix p (min p.batch 31))),
    (7163, b32 (prefixWindow (groupLaneTiles p 0) 32 lane))] ++
  firstLoaderScanFacts p l (warpLane l g lane) warp

/-- After the total broadcast, every loader lane takes the same local first-group branch. -/
theorem loaderFirstRouteLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp lane : Nat} (hg : g < l.threads) (hl : lane < 32) {t : TState}
    (ht : At t 227 ((7164,b32 (prefixWindow (groupLaneTiles p 0) 32
      (shflSource .idx lane 31 31).1)) :: loaderScanFacts p l g warp 5 lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u ∧
      At u (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
        (loaderFirstRouteFacts p l g warp lane) := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  let count := tilePrefix p (min p.batch 31)
  let cta := g / l.block
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLimit : count * p.heads < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hCount : count < 2 ^ 31 := by
    have hPos : 0 < p.heads := by
      have h := hp.shape.2.2.1
      simp [Params.heads]
      omega
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_right count hPos) hLimit
  have hCta : cta < 2 ^ 31 := by
    have hGrid : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact hGrid.trans hp.grid.2.2
  have hCountPart : part 31 = count := by
    change prefixWindow (groupLaneTiles p 0) 32 31 = _
    rw [prefixWindow_warp _ (show (31 : Nat) < 32 by decide)]
    have h := groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    simpa [count, tilePrefix] using h
  let thread := warpLane l g lane
  let carry := (7164, b32 count) :: loaderScanFacts p l g warp 5 lane
  let regs := carry.map Prod.fst
  have hCountWord := ht.2.2.2.2.1
  change t.regs 7164 = some (b32 (part (shflSource .idx lane 31 31).1)) at hCountWord
  rw [shflSource_idx lane (show (31 : Nat) < 32 by decide), hCountPart] at hCountWord
  have hCarry : Holds t.regs carry := ⟨hCountWord, ht.2.2.2.2.2⟩
  have hWarp := (Step.sameWarp_lane hBlock hg hl).1
  have hSame : thread / l.block = cta := hWarp.1.2.2.symm
  have hFrame : Holds t.regs (firstLoaderScanFacts p l thread warp) := hCarry.2.2
  have hHeads := hFrame.2.1
  have hCtaWord := holds_mem hFrame (by
    simp [firstLoaderScanFacts, loaderCuQFacts, loaderEntryFacts] :
      (1072, b32 (thread / l.block)) ∈ firstLoaderScanFacts p l thread warp)
  rw [hSame] at hCtaWord
  have hAt : At t 227
      [(7164, b32 count), (7136, b32 p.heads), (1072, b32 cta)] :=
    ht.mono ⟨hCountWord, hHeads, hCtaWord, trivial⟩
  obtain ⟨u, hu, hU⟩ := loaderFirstLimit l thread hCount hp.heads_signed hCta hLimit _ hAt
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hPreserved := holdsSchedulerFrame hCarry huFrame (fun _ h => List.mem_map_of_mem h)
  let guard := decide (cta < count * p.heads)
  have hBranch : At u 230
      ((73, .pred guard) :: (7166, b32 (count * p.heads)) :: (7165, b32 0) :: carry) :=
    hU.mono ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.2.1, hPreserved⟩
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_230 guard hBranch hBranch.2.2.2.2.1 (by simp)
  obtain ⟨hvA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  refine ⟨v, run_rtg (run_comp huA hvA), ?_⟩
  have hLast : Holds v.regs (loaderFirstRouteFacts p l g warp lane) := by
    unfold loaderFirstRouteFacts
    have h := hV.2.2.2.2.2
    change Holds v.regs
      ((7166, b32 (count * p.heads)) :: (7165, b32 0) :: (7164, b32 count) ::
        loaderScanFacts p l g warp 5 lane) at h
    exact h
  simpa only [guard, cta, count, decide_eq_true_eq, Nat.reduceAdd] using hV.mono hLast

/-- Broadcast the computed total from lane 31, then take the actual first-group branch.
Every lane selects the same path because the total and CTA index are common. -/
theorem loaderFirstRouteTo (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 226 (loaderScanFacts p l g warp 5) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 226 < target.pc) :
    ∃ result : SchedulerWarpAt l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
      (loaderFirstRouteFacts p l g warp) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  let part := prefixWindow (groupLaneTiles p 0) 32
  have hFresh (lane : Nat) (_ : lane < 32) (pair : Nat × Value)
      (hm : pair ∈ loaderScanFacts p l g warp 5 lane) : pair.1 ≠ 7164 := by
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    intro he
    rw [he] at hMem
    exact (of_decide_eq_true rfl : 7164 ∉ (loaderScanFacts p l g warp 5 lane).map Prod.fst) hMem
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl .idx (b32 (part lane)) 31 31
          (fun v _ => next (setReg (cur.state lane) 7164 v))) := by
    have ht := cur.checkpoint lane hl
    refine (loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans ?_
    exact loaderFirstTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1
  obtain ⟨read, hAdvance⟩ := cur.consumeShuffleTo hp hX hg .idx (fun lane => b32 (part lane))
    (fun _ => 31) (fun _ => 31) hFresh hOut hProgress hPc
  obtain ⟨result, hPosition⟩ := read.advanceLocalAt
    (pc' := if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
    (G := loaderFirstRouteFacts p l g warp) (by
    intro lane hl
    exact loaderFirstRouteLocal hp hg hl (read.checkpoint lane hl))
  exact ⟨result, fun h => hPosition.symm ▸ hAdvance h⟩

/-- Start the first tile scan from the observed down-shuffle and route the loader warp. -/
theorem loaderFirstScheduleTo (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 188 (fun lane =>
      (1707, b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
        loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes ends) {src index : Nat}
    {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 226 < target.pc) :
    ∃ result : SchedulerWarpAt l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
      (loaderFirstRouteFacts p l g warp) (shuffles + 6) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨first, hPos⟩ := cur.advanceLocalAt (pc' := 206)
    (G := fun lane => firstLoaderScanFacts p l (warpLane l g lane) warp) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    obtain ⟨_, u, hr, hu⟩ := loaderFirstTiles hp (g := warpLane l g lane)
      (t := cur.state lane) (warp := warp) (by simpa only [hLane] using ht)
    exact ⟨u, run_rtg hr, hu⟩)
  have hFirst : WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g first.pos src index target := fun h => hPos.symm ▸ h
  obtain ⟨scan, hScan⟩ := loaderFirstScanTo hp hX hg first (hProgress.imp_right hFirst) (by omega)
  obtain ⟨route, hRoute⟩ := loaderFirstRouteTo hp hX hg scan
    (hProgress.imp_right (hScan ∘ hFirst)) hPc
  exact ⟨route, hRoute ∘ hScan ∘ hFirst⟩

/-- The first loader schedule on a terminated trace. -/
theorem loaderFirstSchedule (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp shuffles votes : Nat} (hg : g < l.threads)
    (cur : SchedulerWarpAt l X g 188 (fun lane =>
      (1707, b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
        loaderCuQFacts p l (warpLane l g lane) warp) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
      (loaderFirstRouteFacts p l g warp) (shuffles + 6) votes) := by
  obtain ⟨s, _⟩ := loaderFirstScheduleTo hp hX hg cur (src := 0) (index := 0)
    (target := ⟨227, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨s⟩

/-- The real loader trace reaches the first group selection or the fallback scan entry.
Its ten shuffles include the three broadcasts in the common prologue. -/
theorem loaderStartupSchedule (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hComplete : Complete l X) {g : Nat} (hg : g < l.threads) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) :
    Nonempty (SchedulerWarpAt l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
      (loaderFirstRouteFacts p l g (Prologue.warpIndex l g)) 10 0) := by
  obtain ⟨cur⟩ := loaderStartupCuQ hp hX hComplete hg hWarp (hp.cuQ_protected writes)
  exact loaderFirstSchedule hp hX hg cur

end
end PTX.Kernels.TmlFa4Fwd.Loader

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackFold
import Kernels.TmlFa4Fwd.Flow.Code.Part050

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The common registers that feed selection after any populated request-group scan. -/
def groupRouteFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) (first : Nat) :
    List (Nat × Value) :=
  [(7244, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
   (7243, b32 first), (7242, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
   (7241, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
   (7240, b32 (groupLaneTiles p first (laneOf l g)))] ++
    fallbackBaseFrame p l g warp

private theorem fallbackTotalOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (sum : Nat)
    (hpc : t.pc = 3207) (hf : t.fault = none) (hv : t.regs 7241 = some (b32 sum)) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7242 value))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_3207) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7242 none (.reg 7241) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem fallbackLimit (l : Launch) (g : Nat) {count heads cutoff cta : Nat}
    (hHeads : 0 < heads) (hh : heads < 2 ^ 31) (hCta : cta < 2 ^ 31)
    (hLimit : count * heads + cutoff < 2 ^ 31) :
    Seg kernel [] l g 3 3208
      [(7242, b32 count), (7140, b32 heads), (7238, b32 cutoff), (1072, b32 cta)] 3211
      [(7244, b32 (count * heads + cutoff)), (7238, b32 (count * heads + cutoff)),
        (464, .pred (decide (count * heads + cutoff ≤ cta)))] := by
  intro t ht
  have hc : count ≤ count * heads := Nat.le_mul_of_pos_right count hHeads
  have hc32 : count < 2 ^ 32 := by omega
  have hh32 : heads < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  have hCut32 : cutoff < 2 ^ 32 := by omega
  have hTotal32 : count * heads + cutoff < 2 ^ 32 := by omega
  seg_fp ht using
    simp only [b32, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, truncBits_ofNat hc32 (by decide),
      truncBits_ofNat hh32 (by decide), truncBits_ofNat hCta32 (by decide),
      truncBits_ofNat hCut32 (by decide), truncBits_ofNat hTotal32 (by decide),
      compare, Option.getD_some, signedWord hCta, signedWord hLimit, Int.ofNat_le]

private theorem warpFallbackAfterTotal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hGroup : first + 31 < p.batch) {ends : Nat → Option TState}
    (read : SchedulerWarpAt l X g 3208 (fun lane =>
      (7242, b32 (prefixWindow (groupLaneTiles p (first + 31)) 32
        (shflSource .idx lane 31 31).1)) ::
        fallbackFoldFacts p l (warpLane l g lane) warp first
          (tilePrefix p (first + 31) * p.heads) 5) shuffles votes ends) :
    let start := first + 31
    let cutoff := tilePrefix p (min p.batch (start + 31)) * p.heads
    ∃ u : SchedulerWarpAt l X g (if cutoff ≤ g / l.block then 3158 else 3212)
        (fun lane => if cutoff ≤ g / l.block then
          fallbackScanFacts p l (warpLane l g lane) warp start cutoff
        else groupRouteFacts p l (warpLane l g lane) warp start) shuffles votes ends,
      u.pos = read.pos ∧ u.before = read.before := by
  dsimp only
  let t := warpLane l g
  let start := first + 31
  let cta := g / l.block
  let cutoff := tilePrefix p start * p.heads
  let bound := tilePrefix p (min p.batch (start + 31)) * p.heads
  let xs := groupLaneTiles p start
  let part := prefixWindow xs 32
  let count := ∑ i ∈ Finset.range 32, xs i
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCta : cta < 2 ^ 31 := by
    have hGrid : cta < l.grid :=
      (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact hGrid.trans hp.grid.2.2
  have hHeads : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hBound : count * p.heads + cutoff = bound := by
    have h := congrArg (· * p.heads) (groupTiles_eq p hGroup.le (by decide : 32 ≤ 32))
    change (tilePrefix p start + count) * p.heads = bound at h
    simpa only [Nat.add_mul, Nat.add_comm] using h
  have hFit : count * p.heads + cutoff < 2 ^ 31 :=
    hBound.symm ▸ hp.prefixWork_signed (Nat.min_le_left _ _)
  have hCount : part 31 = count := prefixWindow_warp xs (by decide)
  refine read.advanceLocalPreserving (pc' := if bound ≤ cta then 3158 else 3212)
    (G := fun lane => if bound ≤ cta then fallbackScanFacts p l (t lane) warp start bound
      else groupRouteFacts p l (t lane) warp start) ?_
  intro lane hl
  have hSame : t lane / l.block = cta := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  let P := fallbackFoldFacts p l (t lane) warp first cutoff 5
  let keep := [(7242, b32 count),
    (7241, b32 (∑ i ∈ Finset.range (laneOf l (t lane) + 1), xs i)),
    (7243, b32 start), (1217, b32 (t lane / l.block + 1)),
    (7240, b32 (xs (laneOf l (t lane))))] ++
    fallbackBaseFrame p l (t lane) warp
  have ht := read.checkpoint lane hl
  have hWord : (read.state lane).regs 7242 = some (b32 count) := by
    have h := ht.2.2.2.2.1
    rw [shflSource_idx lane (by decide : (31 : Nat) < 32)] at h
    change (read.state lane).regs 7242 = some (b32 (part 31)) at h
    rwa [hCount] at h
  have hF : Holds (read.state lane).regs P := ht.2.2.2.2.2
  have hPart : (read.state lane).regs 7241 =
      some (b32 (∑ i ∈ Finset.range (laneOf l (t lane) + 1), xs i)) := by
    have h := hF.1
    change (read.state lane).regs 7241 =
      some (b32 (prefixWindow xs 32 (laneOf l (t lane)))) at h
    have hLane : laneOf l (t lane) < 32 := Nat.mod_lt _ (by decide)
    rw [prefixWindow_warp xs hLane] at h
    exact h
  have hBase : Holds (read.state lane).regs (fallbackBaseFrame p l (t lane) warp) :=
    hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hOwn := holds_lookup hF
    (show P.lookup 7240 = some (b32 (xs (laneOf l (t lane)))) from rfl)
  have hFirst : (read.state lane).regs 7243 = some (b32 start) := by
    have h := holds_lookup hF (show P.lookup 7243 = some (b32 (min start p.batch)) from rfl)
    rwa [Nat.min_eq_left hGroup.le] at h
  have hSent := holds_lookup hF
    (show P.lookup 1217 = some (b32 (t lane / l.block + 1)) from rfl)
  have hCtaWord : (read.state lane).regs 1072 = some (b32 cta) := by
    rw [← hSame]
    exact holds_lookup hBase rfl
  have hAt : At (read.state lane) 3208
      [(7242, b32 count), (7140, b32 p.heads), (7238, b32 cutoff), (1072, b32 cta)] :=
    ht.mono ⟨hWord, hBase.1, holds_lookup hF (show P.lookup 7238 = _ from rfl),
      hCtaWord, trivial⟩
  obtain ⟨v, hv, hV⟩ := (fallbackLimit l (t lane) hHeads hp.heads_signed hCta hFit).apply hAt
  have hKeep : At (read.state lane) 3208 keep :=
    ht.mono ⟨hWord, hPart, hFirst, hSent, hOwn, hBase⟩
  obtain ⟨hvA, hFrame⟩ := fallbackLinear (by decide) (by decide) hKeep
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  rw [hBound] at hV
  let hit := decide (bound ≤ cta)
  have hBranch : At v 3211 ((464, .pred hit) :: (7244, b32 bound) ::
      (7238, b32 bound) :: keep) :=
    hV.mono ⟨hV.2.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1, hFrame⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t lane)
    Flow.code_3211 hit hBranch hBranch.2.2.2.2.1 (by simp)
  have hwA := Mma.groupScanLocalRun .softmaxSelect (by decide) (by decide) hBranch.1 rfl hw
  have hReg := hW.2.2.2.2
  have hPc : w.pc = if bound ≤ cta then 3158 else 3212 := by
    simpa only [hit, decide_eq_true_eq, Nat.reduceAdd] using hW.1
  refine ⟨w, run_rtg (run_comp hvA hwA), hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1, ?_⟩
  by_cases h : bound ≤ cta
  · rw [ite_eq_left h]
    have hKept : Holds w.regs keep := hReg.2.2.2
    have hSaved : Holds w.regs (fallbackBaseFrame p l (t lane) warp) := hKept.2.2.2.2.2
    exact ⟨hReg.2.2.1, hKept.2.2.1, holds_lookup hSaved rfl, hKept.2.2.2.1,
      holds_lookup hSaved rfl, hSaved⟩
  · rw [ite_eq_right h]
    exact ⟨hReg.2.1, hReg.2.2.2.2.2.1, hReg.2.2.2.1, hReg.2.2.2.2.1,
      hReg.2.2.2.2.2.2.2.1, hReg.2.2.2.2.2.2.2.2⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g first shuffles votes : Nat} {warp : Fin 8}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3207 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first
        (tilePrefix p (first + 31) * p.heads) 5) shuffles votes ends) {src index : Nat}
    {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
include hp hX hg hGroup cur hProgress

/-- The actual lane-31 broadcast and signed comparison select this group or continue scanning. -/
theorem warpFallbackRouteToRecorded (hTarget : 3207 < target.pc) :
    let start := first + 31
    let cutoff := tilePrefix p (min p.batch (start + 31)) * p.heads
    ∃ u : SchedulerWarpAt l X g (if cutoff ≤ g / l.block then 3158 else 3212)
        (fun lane => if cutoff ≤ g / l.block then
          fallbackScanFacts p l (warpLane l g lane) warp start cutoff
        else groupRouteFacts p l (warpLane l g lane) warp start) (shuffles + 1) votes ends,
      u.pos = (fun lane => cur.pos lane + 1) ∧
      (∀ lane < 32, u.pos lane ≤ (X.tr (warpLane l g lane)).length) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g u.pos src index target) := by
  dsimp only
  let t := warpLane l g
  let start := first + 31
  let cutoff := tilePrefix p start * p.heads
  let xs := groupLaneTiles p start
  let part := prefixWindow xs 32
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hFresh : ∀ lane < 32, ∀ x ∈ fallbackFoldFacts p l (t lane) warp first cutoff 5,
      x.1 ≠ 7242 := by
    intro lane hl
    exact of_decide_eq_true rfl
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (t lane) (cur.state lane) =
        .ev (.shfl .idx (b32 (part lane)) 31 31
          (fun v _ => next (setReg (cur.state lane) 7242 v))) := by
    have ht := cur.checkpoint lane hl
    have h := ht.2.2.2.2.1
    change (cur.state lane).regs 7241 = some (b32 (part (laneOf l (t lane)))) at h
    rw [show laneOf l (t lane) = lane from (Step.sameWarp_lane hBlock hg hl).2] at h
    exact fallbackTotalOut hp _ ht.1 ht.2.2.2.1 h
  obtain ⟨read, hPos, hEvent, hRead⟩ :=
    cur.consumeShuffleToRecorded hp hX hg .idx (fun lane => b32 (part lane))
    (fun _ => 31) (fun _ => 31) hFresh hOut hProgress hTarget
  obtain ⟨u, hu, _⟩ := warpFallbackAfterTotal hp hg hGroup read
  refine ⟨u, hu.trans hPos, ?_, fun h => hu.symm ▸ hRead h⟩
  intro lane hl
  obtain ⟨_, _, he⟩ := hEvent lane hl
  rw [hu, hPos]
  exact len_of_get he

theorem warpFallbackRouteTo (hTarget : 3207 < target.pc) :
    let start := first + 31
    let cutoff := tilePrefix p (min p.batch (start + 31)) * p.heads
    ∃ u : SchedulerWarpAt l X g (if cutoff ≤ g / l.block then 3158 else 3212)
        (fun lane => if cutoff ≤ g / l.block then
          fallbackScanFacts p l (warpLane l g lane) warp start cutoff
        else groupRouteFacts p l (warpLane l g lane) warp start) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g u.pos src index target := by
  obtain ⟨u, _, _, hFollow⟩ := warpFallbackRouteToRecorded hp hX hg hGroup cur hProgress hTarget
  exact ⟨u, hFollow⟩
end

/-- The actual later-group total determines the next scheduler state in a maximal execution. -/
theorem warpFallbackRouteOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hGroup : first + 31 < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3207 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first
        (tilePrefix p (first + 31) * p.heads) 5) shuffles votes ends) :
    let start := first + 31
    let cutoff := tilePrefix p (min p.batch (start + 31)) * p.heads
    Nonempty (SchedulerWarpReached l X g (if cutoff ≤ g / l.block then 3158 else 3212)
      (fun lane => if cutoff ≤ g / l.block then
        fallbackScanFacts p l (warpLane l g lane) warp start cutoff
      else groupRouteFacts p l (warpLane l g lane) warp start) (shuffles + 1) votes ends) := by
  dsimp only
  let t := warpLane l g
  let start := first + 31
  let cutoff := tilePrefix p start * p.heads
  let xs := groupLaneTiles p start
  let part := prefixWindow xs 32
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hFresh : ∀ lane < 32, ∀ x ∈ fallbackFoldFacts p l (t lane) warp first cutoff 5,
      x.1 ≠ 7242 := by
    intro lane hl
    exact of_decide_eq_true rfl
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (t lane) (cur.state lane) =
        .ev (.shfl .idx (b32 (part lane)) 31 31
          (fun v _ => next (setReg (cur.state lane) 7242 v))) := by
    have ht := cur.checkpoint lane hl
    have h := ht.2.2.2.2.1
    change (cur.state lane).regs 7241 = some (b32 (part (laneOf l (t lane)))) at h
    rw [show laneOf l (t lane) = lane from (Step.sameWarp_lane hBlock hg hl).2] at h
    exact fallbackTotalOut hp _ ht.1 ht.2.2.2.1 h
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .idx (fun lane => b32 (part lane))
    (fun _ => 31) (fun _ => 31) hFresh hOut
  obtain ⟨u, hPos, hState⟩ := warpFallbackAfterTotal hp hg hGroup read.toSchedulerWarpAt
  exact ⟨read.reframe u hPos hState⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackUp

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Epilogue Prologue Mma

private theorem totalTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {sum : Nat} (ht : At t 2037 [(7197, b32 sum)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 sum) 31 31
      (fun value _ => next (setReg t 7198 value))) := by
  rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_2037) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 7198 none (.reg 7197) (.imm 31) (.imm 31) (.imm (-1))) = _
  have hb : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, ht.2.2.2.2.1, hb, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem cutoffSegment (l : Launch) (g : Nat) {count heads cutoff cta : Nat}
    (hHeads : 0 < heads) (hh : heads < 2 ^ 31) (hCta : cta < 2 ^ 31)
    (hLimit : count * heads + cutoff < 2 ^ 31) :
    Seg kernel [] l g 3 2038
      [(7198, b32 count), (7139, b32 heads), (7194, b32 cutoff), (1072, b32 cta)] 2041
      [(7200, b32 (count * heads + cutoff)), (7194, b32 (count * heads + cutoff)),
        (360, .pred (decide (count * heads + cutoff ≤ cta)))] := by
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

def mmaFallbackCutoff (p : Params) (first : Nat) : Nat :=
  tilePrefix p (min p.batch (first + 31)) * p.heads

noncomputable def mmaSelectedGroupFacts (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  let xs := groupLaneTiles p first
  [(7200, b32 (mmaFallbackCutoff p first)), (7199, b32 first), (7203, b32 p.batch),
    (1072, b32 (g / l.block)), (7198, b32 (∑ i ∈ Finset.range 32, xs i)),
    (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), xs i)),
    (7196, b32 (xs (laneOf l g)))] ++ fallbackAbi p l g

def mmaFallbackBackedgeFacts (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  groupScanFacts .select first p.batch (g / l.block) ++
    (7194, b32 (mmaFallbackCutoff p first)) :: fallbackAbi p l g

/-- The lane-31 broadcast supplies the exact cutoff, selecting the current group or
returning to the group-search loop with that cutoff as its subsequent input. -/
theorem fallbackRouteOfMaximal {l : Launch} {p : Params} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first ordinal : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    (cur : ∀ h, SameWarp l g h → FallbackScanCursor l X h 2037 ordinal
      (fallbackUpFacts p l h first 5)) :
    let more := mmaFallbackCutoff p first ≤ g / l.block
    Nonempty (FallbackScanCursor l X g (if more then 1988 else 2042) (ordinal + 1)
      (if more then mmaFallbackBackedgeFacts p l g first
        else mmaSelectedGroupFacts p l g first)) := by
  dsimp only
  let xs := groupLaneTiles p first
  let count := ∑ i ∈ Finset.range 32, xs i
  let cta := g / l.block
  let old := tilePrefix p first * p.heads
  let cutoff := mmaFallbackCutoff p first
  let F := [(7199, b32 first), (7203, b32 p.batch), (1182, b32 (cta + 1)), (1072, b32 cta),
    (7198, b32 count), (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), xs i)),
    (7196, b32 (xs (laneOf l g)))] ++ fallbackAbi p l g
  obtain ⟨read⟩ := FallbackScanCursor.shuffleOfMaximal hp hMax hg .idx 31 31
    (fun h => fallbackUpFacts p l h first 5) (fun lane => b32 (prefixWindow xs 32 lane)) cur
    (fun h hWarp => totalTemplate hp
      ((cur h hWarp).checkpoint.mono ⟨(cur h hWarp).checkpoint.2.2.2.2.1, trivial⟩))
    (of_decide_eq_true rfl)
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hBound : count * p.heads + old = cutoff := by
    have h := congrArg (· * p.heads) (groupTiles_eq p hFirst (by decide : 32 ≤ 32))
    change (tilePrefix p first + count) * p.heads = cutoff at h
    simpa only [Nat.add_mul, Nat.add_comm] using h
  have hFit : count * p.heads + old < 2 ^ 31 :=
    hBound.symm ▸ hp.prefixWork_signed (Nat.min_le_left _ _)
  have hCta : cta < 2 ^ 31 :=
    ((Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg).trans hp.grid.2.2
  have hHeads : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  let P := (7198, b32 (prefixWindow xs 32 (shflSource .idx (laneOf l g) 31 31).1)) ::
    fallbackUpFacts p l g first 5
  have hP : At read.state 2038 P := read.checkpoint
  have hWord : read.state.regs 7198 = some (b32 count) := by
    simpa only [shflSource_idx _ (by decide : 31 < 32), prefixWindow_warp _ (by decide : 31 < 32)]
      using holds_lookup hP.2.2.2.2 (show P.lookup 7198 = _ from rfl)
  have hPart : read.state.regs 7197 =
      some (b32 (∑ i ∈ Finset.range (laneOf l g + 1), xs i)) := by
    have h : read.state.regs 7197 = some (b32 (prefixWindow xs 32 (laneOf l g))) :=
      holds_lookup hP.2.2.2.2 rfl
    simpa only [prefixWindow_warp _ hLane] using h
  have hAt : At read.state 2038
      [(7198, b32 count), (7139, b32 p.heads), (7194, b32 old), (1072, b32 cta)] :=
    hP.mono ⟨hWord, holds_lookup hP.2.2.2.2 rfl, holds_lookup hP.2.2.2.2 rfl,
      holds_lookup hP.2.2.2.2 rfl, trivial⟩
  obtain ⟨v, hv, hV⟩ := cutoffSegment l g hHeads hp.heads_signed hCta hFit read.state hAt
  rw [hBound] at hV
  have hF : At read.state 2038 F := by
    apply hP.mono
    change Holds read.state.regs ([(7199, _), (7203, _), (1182, _), (1072, _), (7198, _),
      (7197, _), (7196, _)] ++ fallbackAbi p l g)
    refine ⟨holds_lookup hP.2.2.2.2 rfl, holds_lookup hP.2.2.2.2 rfl,
      holds_lookup hP.2.2.2.2 rfl, holds_lookup hP.2.2.2.2 rfl, hWord, hPart,
      holds_lookup hP.2.2.2.2 rfl, ?_⟩
    exact hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hWrites : ((kernel.code.drop 2038).take 3).all
      (fun i => [7199, 7203, 1182, 1072, 7198, 7197, 7196, 1180, 7139, 2535, 7502, 7506, 7503].all
        (fun r => !(writesRegs i.op).contains r)) = true := by decide +kernel
  have hStraight : ((kernel.code.drop 2038).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by decide +kernel
  have hKeep := holdsSchedulerFrame hF.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrites hStraight hv hAt.1.ge (by rw [hAt.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  let more := decide (cutoff ≤ cta)
  have hBranch : At v 2041 ((360, .pred more) :: (7200, b32 cutoff) :: (7194, b32 cutoff) :: F) :=
    hV.mono ⟨hV.2.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1, hKeep⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2041 more hBranch hBranch.2.2.2.2.1 (by simp)
  have hGo := run_comp (localRun (pc := 2038) (n := 3) (by decide) (by decide)
    hAt.1 hStraight hv) (localRun (pc := 2041) (n := 1) (by decide) (by decide) hBranch.1 rfl hw)
  have hPc : w.pc = if cutoff ≤ cta then 1988 else 2042 := by
    simpa only [more, decide_eq_true_eq, Nat.reduceAdd] using hW.1
  refine ⟨⟨read.pos, read.before, w, read.lastState, read.pos_pos, read.pos_le,
    read.shuffleCount, read.ballotCount, read.released,
    ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1, ?_⟩, read.runPrefix,
    read.localSteps.trans (run_rtg hGo), read.continuation⟩⟩
  have hRegs := hW.2.2.2.2
  have hFrame : Holds w.regs F := hRegs.2.2.2
  have hAbi := hFrame.2.2.2.2.2.2.2
  by_cases h : cutoff ≤ cta
  · rw [ite_eq_left h]
    exact ⟨hFrame.1, hFrame.2.1, hFrame.2.2.1, hFrame.2.2.2.1, hRegs.2.2.1, hAbi⟩
  · rw [ite_eq_right h]
    exact ⟨hRegs.2.1, hFrame.1, hFrame.2.1, hFrame.2.2.2.1, hFrame.2.2.2.2.1,
      hFrame.2.2.2.2.2.1, hFrame.2.2.2.2.2.2.1, hAbi⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation

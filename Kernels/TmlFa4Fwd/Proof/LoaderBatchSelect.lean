-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderLaterRoute
public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The decoded ballot comparison marks precisely the lanes preceding the selected batch. -/
private theorem loaderGroupBallot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {first batch lane cta : Nat} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch) (hLane : lane < 32)
    (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 4 293
      [(7164, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
       (7163, b32 (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i)),
       (7166, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
       (7136, b32 p.heads), (1072, b32 cta)] 297
      [(1079, b32 (tilePrefix p first * p.heads)),
       (89, .pred (decide (first + lane < batch)))] := by
  let start := tilePrefix p first * p.heads
  let tail := tilePrefix p (min p.batch (first + 31)) * p.heads
  let total := ∑ i ∈ Finset.range 32, groupLaneTiles p first i
  let part := ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  have hStart : start < 2 ^ 31 := hp.prefixWork_signed (by omega)
  have hTail : tail < 2 ^ 31 := hp.prefixWork_signed (Nat.min_le_left _ _)
  have hPart : part * p.heads + start < 2 ^ 31 := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by omega : lane + 1 ≤ 32))
    change (tilePrefix p first + part) * p.heads = _ at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h ▸ hp.prefixWork_signed (Nat.min_le_left _ _)
  have hTotal : total * p.heads + start = tail := by
    have h := congrArg (fun n => n * p.heads) (groupTiles_eq p (by omega : first ≤ p.batch)
      (by decide : 32 ≤ 32))
    change (tilePrefix p first + total) * p.heads = tail at h
    rw [Nat.add_mul, Nat.add_comm] at h
    exact h
  have hBallot : part * p.heads + start ≤ cta ↔ first + lane < batch := by
    simpa only [Nat.add_mul, Nat.add_comm, start] using
      groupBallot_iff p hFirst hGroup hBatch hLane hLo hHi
  have hHeads := hp.heads_signed
  have hCta : cta < 2 ^ 31 := lt_trans hHi (hp.prefixWork_signed (by omega))
  have hPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hTotal32 : total < 2 ^ 32 := by have := Nat.le_mul_of_pos_right total hPos; omega
  have hPart32 : part < 2 ^ 32 := by have := Nat.le_mul_of_pos_right part hPos; omega
  have hTail32 : tail < 2 ^ 32 := by omega
  have hHeads32 : p.heads < 2 ^ 32 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  have hTotalWork32 : total * p.heads < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hPartWork32 : part * p.heads + start < 2 ^ 32 := by omega
  have hSub : tail - total * p.heads = start := by omega
  intro t ht
  change At t 293
    [(7164, b32 total), (7163, b32 part), (7166, b32 tail), (7136, b32 p.heads), (1072, b32 cta)]
    at ht
  change ∃ u, run kernel [] l g 4 t = some u ∧
    At u 297 [(1079, b32 start), (89, .pred (decide (first + lane < batch)))]
  seg_fp ht using
    simp only [b32, truncBits_ofNat hTotal32 (by decide), truncBits_ofNat hPart32 (by decide),
      truncBits_ofNat hTail32 (by decide), truncBits_ofNat hHeads32 (by decide),
      truncBits_ofNat hCta32 (by decide), truncBits_ofNat hStart32 (by decide),
      ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
      truncBits_ofNat hTotalWork32 (by decide), truncBits_ofNat hPartWork32 (by decide),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show total * p.heads < 2 ^ 64 by omega)
        (show total * p.heads ≤ tail by omega),
      hSub, compare, Option.getD_some, signedWord hPart, signedWord hCta,
      Int.ofNat_le, hBallot]

/-- The decoded selection ballot returns its mask in the loader scratch register. -/
theorem loaderGroupVote {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hit : Bool)
    (hpc : t.pc = 297) (hf : t.fault = none) (hv : t.regs 89 = some (.pred hit)) :
    out kernel [] l g t = .ev (.vote (2 ^ 32 - 1) hit
      (fun mask => next (setReg t 1751 (b32 mask.toNat)))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_297) rfl rfl]
  change Out.ev (voteTmpl l g t 1751 89 false (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [voteTmpl, readPred, readReg, hv, hBlock, bind, Except.bind, pure, Except.pure, b32]
  rfl

private theorem loaderGroupPopcount (l : Launch) (g : Nat) {first n : Nat}
    (hn : n < 32) (hbound : first + n < 2 ^ 31) :
    Seg kernel [] l g 4 298 [(1751, b32 (2 ^ n - 1)), (7165, b32 first)] 302
      [(1080, b32 n), (7170, b32 (first + n)), (90, .pred (decide (n = 0))),
       (7167, b32 0)] := by
  intro t ht
  have hp : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
  have hMask : 2 ^ n - 1 < 2 ^ 32 := by omega
  have hMask64 : 2 ^ n - 1 < 2 ^ 64 := by omega
  have hFirst : first < 2 ^ 32 := by omega
  have hSum : first + n < 2 ^ 32 := by omega
  have hn32 : n < 2 ^ 32 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have hzMask : 2 ^ n - 1 = 0 ↔ n = 0 := by
    cases n with
    | zero => decide
    | succ n =>
      have hOne := Nat.one_lt_two_pow (Nat.succ_ne_zero n)
      omega
  have hc := ballotPrefixPopcount (Nat.le_of_lt hn)
  seg_fp ht using
    first
    | rfl
    | (simp only [b32, truncBits_ofNat hMask (by decide), truncBits_ofNat hFirst (by decide),
        toNat_ofNat_lt hMask64, hc, truncBits_ofNat hn32 (by decide), ← BitVec.ofNat_add,
        truncBits_ofNat hSum (by decide), Nat.add_comm,
        compare, Option.getD_some, hz, Int.natCast_eq_zero, hzMask])

/-- A nonexhausted loader group sets the default coordinates and falls through to the ballot. -/
private theorem loaderGroupAvailable (l : Launch) (g : Nat) {first batch : Nat}
    (hGroup : first < batch) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 5 288 [(7165, b32 first), (7170, b32 batch)] 293
      [(771, .pred false), (7168, b32 0), (7169, b32 0)] := by
  intro t ht
  have hf : first < 2 ^ 31 := by omega
  obtain ⟨u, hu, hU⟩ : ∃ u, run kernel [] l g 4 t = some u ∧
      At u 292 [(88, .pred false), (771, .pred false), (7168, b32 0), (7169, b32 0)] := by
    seg_fp ht using
      first
      | rfl
      | simp only [compare, Option.getD_some, truncBits_ofNat (show first < 2 ^ 32 by omega)
          (by decide), truncBits_ofNat (show batch < 2 ^ 32 by omega) (by decide),
          signedWord hf, signedWord hBatch, ge_iff_le, Int.ofNat_le,
          decide_eq_false (Nat.not_le_of_lt hGroup)]
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_292 false hU hU.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hu hv, hV.mono hV.2.2.2.2.2⟩

/-- Registers live from a ready group through its request selection ballot. -/
def loaderVoteCarry (p : Params) (l : Launch) (g warp first lane : Nat) :
    List (Nat × Value) :=
  [(7168, b32 0), (7169, b32 0), (771, .pred false),
    (7165, b32 first), (7162, b32 (groupLaneTiles p first lane)),
    (7163, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7136, b32 p.heads)] ++ loaderCuQFacts p l (warpLane l g lane) warp

/-- Registers kept after the popcount. The batch-limit register now holds the selected batch. -/
def loaderChosenFacts (p : Params) (l : Launch) (g warp first batch lane : Nat) :
    List (Nat × Value) :=
  [(1080, b32 (batch - first)), (7170, b32 batch), (90, .pred (decide (batch = first))),
    (7167, b32 0), (1079, b32 (tilePrefix p first * p.heads))] ++
    (loaderVoteCarry p l g warp first lane).filter (fun pair => pair.1 != 7170)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g warp first batch shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
include hp hg hFirst hGroup hBatch hLo hHi

/-- A nonexhausted group reaches the actual selection ballot with the mathematically
selected request's lane comparison. -/
theorem loaderGroupBallotReadyPreserving {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 288 (loaderLaterChoiceFacts p l g warp first) shuffles votes ends)
    :
    ∃ next : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (first + lane < batch))) ::
        (1079, b32 (tilePrefix p first * p.heads)) ::
        loaderVoteCarry p l g warp first lane) shuffles votes ends,
      next.pos = cur.pos ∧ next.before = cur.before := by
  let cta := g / l.block
  have hf : first < p.batch := hFirst.trans_lt hBatch
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let keep := (loaderLaterChoiceFacts p l g warp first lane).map Prod.fst
  have ht := cur.checkpoint lane hl
  have hFact := ht.2.2.2.2
  have hAbi : Holds (cur.state lane).regs (loaderCuQFacts p l thread warp) :=
    hFact.2.2.2.2.2.2
  have hAvailable : At (cur.state lane) 288 [(7165, b32 first), (7170, b32 p.batch)] :=
    ht.mono ⟨hFact.2.1, hAbi.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := loaderGroupAvailable l thread hf hp.shape.2.1 _ hAvailable
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hSave := holdsSchedulerFrame hFact huFrame (fun _ h => List.mem_map_of_mem h)
  have hHead : u.regs 7136 = some (b32 p.heads) := hSave.2.2.2.2.2.1
  have hSame : thread / l.block = cta := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  have hCta : u.regs 1072 = some (b32 cta) := by
    have h := hSave.2.2.2.2.2.2.2.2.2.1
    rw [hSame] at h
    exact h
  have hTotal : u.regs 7164 = some (b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)) :=
    hSave.2.2.1
  have hPart := hSave.2.2.2.1
  change u.regs 7163 = some (b32 (prefixWindow (groupLaneTiles p first) 32 lane)) at hPart
  rw [prefixWindow_warp _ hl] at hPart
  have hCount : u.regs 7162 = some (b32 (groupLaneTiles p first lane)) :=
    hSave.2.2.2.2.1
  obtain ⟨v, hv, hV⟩ := loaderGroupBallot hp thread hFirst hGroup
    hBatch hl hLo hHi u (hU.mono ⟨hTotal, hPart, hSave.1, hHead, hCta, trivial⟩)
  let carry := loaderVoteCarry p l g warp first lane
  let regs := carry.map Prod.fst
  have hCarry : Holds u.regs carry :=
    ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.2.2.1, hU.2.2.2.2.1,
      hSave.2.1, hCount, hPart, hHead, hSave.2.2.2.2.2.2⟩
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hU.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hSaved := holdsSchedulerFrame hCarry hvFrame (fun _ h => List.mem_map_of_mem h)
  exact ⟨v, run_rtg (run_comp huA hvA),
    hV.mono ⟨hV.2.2.2.2.2.1, hV.2.2.2.2.1, hSaved⟩⟩

/-- The group preparation retains the actual trace positions. -/
theorem loaderGroupBallotReadyAt {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 288 (loaderLaterChoiceFacts p l g warp first) shuffles votes ends)
    :
    ∃ next : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (first + lane < batch))) ::
        (1079, b32 (tilePrefix p first * p.heads)) ::
        loaderVoteCarry p l g warp first lane) shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := loaderGroupBallotReadyPreserving hp hg hFirst hGroup hBatch hLo hHi cur
  exact ⟨next,hPos⟩

/-- The selection ballot in a terminated run. -/
theorem loaderGroupBallotReady
    (cur : SchedulerWarpAt l X g 288 (loaderLaterChoiceFacts p l g warp first) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (first + lane < batch))) :: (1079, b32 (tilePrefix p first * p.heads)) ::
        loaderVoteCarry p l g warp first lane) shuffles votes) := by
  obtain ⟨ready, _⟩ := loaderGroupBallotReadyAt hp hg hFirst hGroup hBatch hLo hHi cur
  exact ⟨ready⟩
end

private theorem firstBallotFacts_eq (p : Params) (l : Launch) (g warp batch : Nat) :
    (fun lane => (89, .pred (decide (0 + lane < batch))) ::
      (1079, b32 (tilePrefix p 0 * p.heads)) :: loaderVoteCarry p l g warp 0 lane) =
      (fun lane => (89, .pred (decide (lane < batch))) ::
        (1079, b32 0) :: loaderVoteCarry p l g warp 0 lane) := by
  funext lane
  simp [tilePrefix]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g warp batch shuffles votes : Nat} (hg : g < l.threads) (hGroup : batch < 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
include hp hg hGroup hBatch hLo hHi

/-- The first scheduler branch reaches the actual selection ballot with the mathematically
selected request's lane comparison. -/
theorem loaderFirstBallotReadyPreserving {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 288 (loaderFirstRouteFacts p l g warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (lane < batch))) :: (1079, b32 0) ::
        loaderVoteCarry p l g warp 0 lane) shuffles votes ends,
      next.pos = cur.pos ∧ next.before = cur.before := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨state,hPos,hBefore⟩ := cur.advanceLocalPreserving (pc' := 288)
    (G := loaderLaterChoiceFacts p l g warp 0) (by
    intro lane hl
    have ht := cur.checkpoint lane hl
    have h := ht.2.2.2.2
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hTile := h.2.2.2.2.1
    rw [hLane] at hTile
    have hSum := groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    have he : (∑ i ∈ Finset.range 32, groupLaneTiles p 0 i) = tilePrefix p (min p.batch 31) :=
      by simpa [tilePrefix] using hSum
    have hTotal := h.2.2.1
    rw [← he] at hTotal
    exact ⟨_, .refl, ht.mono ⟨h.1, h.2.1, hTotal, h.2.2.2.1, hTile, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2⟩⟩)
  have hReady := loaderGroupBallotReadyPreserving hp hg (Nat.zero_le batch)
    (show batch < 0 + 31 from hGroup) hBatch hLo hHi state
  rw [hPos,hBefore] at hReady
  rw [firstBallotFacts_eq p l g warp batch] at hReady
  exact hReady

private theorem loaderFirstBallotReadyAt {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 288 (loaderFirstRouteFacts p l g warp) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (lane < batch))) :: (1079, b32 0) ::
        loaderVoteCarry p l g warp 0 lane) shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := loaderFirstBallotReadyPreserving hp hg hGroup hBatch hLo hHi cur
  exact ⟨next,hPos⟩

end

/-- The next event from the prepared selection cursor is its ballot. -/
theorem loaderSelectionNext {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g warp first batch shuffles votes : Nat}
    {ends : Nat → Option TState} (cur : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (first + lane < batch))) ::
        (1079, b32 (tilePrefix p first * p.heads)) ::
        loaderVoteCarry p l g warp first lane) shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    Next kernel Assumptions.all l (warpLane l g lane) (cur.before lane) (cur.state lane)
      (.vote (2 ^ 32 - 1) (decide (first+lane < batch))
        (fun word => next (setReg (cur.state lane) 1751 (b32 word.toNat)))) := by
  have ht := cur.checkpoint lane hl
  have hOut := loaderGroupVote hp (warpLane l g lane) (cur.state lane) (decide (first+lane < batch))
    ht.1 ht.2.2.2.1 ht.2.2.2.2.1
  exact ⟨cur.localSteps lane hl, (loaderOutCore (by rw [ht.1]; decide)
    (by rw [ht.1]; decide)).trans hOut⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g warp first batch shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (first + lane < batch))) ::
        (1079, b32 (tilePrefix p first * p.heads)) ::
        loaderVoteCarry p l g warp first lane) shuffles votes ends)
include hp hX hg hFirst hGroup hBatch cur

/-- Consume an already recorded loader ballot, retaining its exact returned boundary. -/
theorem loaderSelectBatchPresent
    (hMore : ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ []) :
    ∃ result : SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp first batch)
      shuffles (votes + 1) ends, result.pos = (fun lane => cur.pos lane + 1) ∧
      ∀ lane < 32, ∃ word,
        X.get (warpLane l g lane,cur.pos lane) =
          some ⟨297,.vote (2 ^ 32 - 1) (decide (first+lane < batch)) word⟩ ∧
        result.before lane = next (setReg (cur.state lane) 1751 (b32 word.toNat)) := by
  let thread := warpLane l g
  let hit := fun lane => decide (first + lane < batch)
  let after := fun (lane : Nat) (word : BitVec 32) =>
    next (setReg (cur.state lane) 1751 (b32 word.toNat))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hVote (lane : Nat) : ∃ word, lane < 32 →
      X.get (thread lane, cur.pos lane) = some ⟨297, .vote (2 ^ 32 - 1) (hit lane) word⟩ ∧
        Run kernel Assumptions.all l (thread lane) (after lane word)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨word, he, _, hr⟩ := (loaderSelectionNext hp cur lane hl).ballot_at_nonempty
        (cur.continuation lane hl) (hMore lane hl) (cur.ordinals.vote lane hl)
      rw [(cur.checkpoint lane hl).1] at he
      exact ⟨word, fun _ => ⟨he, hr⟩⟩
    · exact ⟨0, fun h => (hl h).elim⟩
  choose word obs using hVote
  obtain ⟨hOrdinal, _, hOrd⟩ := cur.ordinals.ballot (fun _ => 297) hit word
    (fun lane hl => (obs lane hl).1)
  let pos := fun lane => cur.pos lane + 1
  let n := batch - first
  have hn : n < 32 := by omega
  have hBatch31 := hp.shape.2.1
  have hnAdd : first + n = batch := by dsimp [n]; omega
  have hBound : first + n < 2 ^ 31 := by omega
  have hLocal (lane : Nat) : ∃ v, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane))
        (after lane (word lane)) v ∧
        At v 302 (loaderChosenFacts p l g warp first batch lane) := by
    by_cases hl : lane < 32
    · have hLane : laneOf l (thread lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hPeers (j : Nat) (hj : j < 32) : ∃ k val,
          let e := (thread lane - laneOf l (thread lane) + j, k)
          X.get e = some ⟨297, .vote (2 ^ 32 - 1) (hit j) val⟩ ∧
            X.MaskK voteClass e (2 ^ 32 - 1) votes := by
        refine ⟨cur.pos j, word j, ?_⟩
        dsimp only
        have he : thread lane - laneOf l (thread lane) + j = thread j := by
          rw [hLane]
          simp only [thread, warpLane]
          omega
        rw [he]
        exact ⟨(obs j hj).1, hOrdinal j hj⟩
      have hWord := selectedGroupMask hX hFirst (obs lane hl).1 (hOrdinal lane hl) hPeers
      have hValue : (word lane).toNat = 2 ^ n - 1 := by
        rw [hWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact lt_of_le_of_lt (Nat.sub_le ..) (Nat.pow_lt_pow_right (by decide) hn)
      have ht := cur.checkpoint lane hl
      have hFresh (pair : Nat × Value) (hm : pair ∈
          (89, .pred (hit lane)) :: (1079, b32 (tilePrefix p first * p.heads)) ::
            loaderVoteCarry p l g warp first lane) : pair.1 ≠ 1751 := by
        intro he
        have hm' := List.mem_map_of_mem (f := Prod.fst) hm
        rw [he] at hm'
        exact (of_decide_eq_true rfl : 1751 ∉
          89 :: 1079 :: (loaderVoteCarry p l g warp first lane).map Prod.fst) hm'
      have ha := ht.set (v := b32 (word lane).toNat) hFresh
      have hChosen : At (after lane (word lane)) 298
          [(1751, b32 (2 ^ n - 1)), (7165, b32 first)] := by
        refine ha.mono ⟨?_, ha.2.2.2.2.2.2.2.2.2.2.1, trivial⟩
        rw [← hValue]
        exact ha.2.2.2.2.1
      let carry := (loaderVoteCarry p l g warp first lane).filter (fun pair => pair.1 != 7170)
      let frame := (1079, b32 (tilePrefix p first * p.heads)) :: carry
      let regs := frame.map Prod.fst
      have hCarry := ha.2.2.2.2.2.2.2
      have hKeep : Holds (after lane (word lane)).regs frame := by
        refine ⟨ha.2.2.2.2.2.2.1, ?_⟩
        have hFilter {F : List (Nat × Value)} (h : Holds (after lane (word lane)).regs F) :
            Holds (after lane (word lane)).regs (F.filter (fun pair => pair.1 != 7170)) := by
          induction F with
          | nil => trivial
          | cons a as ih =>
            rw [List.filter_cons]
            by_cases ha : (a.1 != 7170) = true
            · simp only [ha, ↓reduceIte]
              exact ⟨h.1, ih h.2⟩
            · simp only [ha]
              exact ih h.2
        exact hFilter hCarry
      obtain ⟨v, hv, hV⟩ := loaderGroupPopcount l (thread lane) hn hBound
        (after lane (word lane)) hChosen
      obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := regs) (by decide) (by decide) hChosen.1
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hv
      have hSaved := holdsSchedulerFrame hKeep hvFrame (fun _ h => List.mem_map_of_mem h)
      have hZ : n = 0 ↔ batch = first := by dsimp [n]; omega
      exact ⟨v, fun _ => ⟨run_rtg hvA, hV.mono
        ⟨hV.2.2.2.2.1, by simpa only [hnAdd] using hV.2.2.2.2.2.1,
        by simpa only [hZ] using hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.1, hSaved⟩⟩⟩
    · exact ⟨after lane (word lane), fun h => (hl h).elim⟩
  choose state h using hLocal
  exact ⟨⟨pos,fun lane => after lane (word lane),state,hOrd,
    fun lane hl => (obs lane hl).2,fun lane hl => (h lane hl).1,fun lane hl => (h lane hl).2⟩,
    rfl,fun lane hl => ⟨word lane,(obs lane hl).1,rfl⟩⟩

/-- Consume each actual PC 297 vote and replay its returned mask through the decoded
popcount, preserving the common collective ordinal of the warp. -/
theorem loaderSelectBatchTo {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 297 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp first batch)
      shuffles (votes + 1) ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hMore : ∀ lane < 32, (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with hDone | h
    · intro lane hl hNil
      have hr := cur.continuation lane hl
      rw [hNil, hDone lane hl] at hr
      cases hr
    · exact h.ballotSuffix hX cur.ordinals hBlock hg (loaderSelectionNext hp cur src h.lane)
        (cur.continuation src h.lane)
  obtain ⟨result,hPos,hEvents⟩ := loaderSelectBatchPresent hp hX hg hFirst hGroup hBatch cur hMore
  refine ⟨result,?_⟩
  intro follows
  rw [hPos]
  exact follows.afterCommonEvent hX hBlock hg hPc (fun lane hl => by
    obtain ⟨word,he,_⟩ := hEvents lane hl
    exact ⟨_,he,rfl,by intro h; cases h⟩)
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The selected batch on a terminated trace. -/
theorem loaderSelectBatch {g warp first batch shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (cur : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (first + lane < batch))) ::
        (1079, b32 (tilePrefix p first * p.heads)) ::
        loaderVoteCarry p l g warp first lane) shuffles votes) :
    Nonempty (SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp first batch)
      shuffles (votes + 1)) := by
  obtain ⟨ready, _⟩ := loaderSelectBatchTo hp hX hg hFirst hGroup hBatch cur
    (src := 0) (index := 0) (target := ⟨298, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨ready⟩

/-- A CTA in the first group's interval reaches the selected batch's actual post-ballot state. -/
theorem loaderFirstBatchTo {g warp shuffles votes : Nat} (hg : g < l.threads)
    (hCta : g / l.block < tilePrefix p (min p.batch 31) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 288 (loaderFirstRouteFacts p l g warp) shuffles votes ends)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 297 < target.pc) :
    ∃ batch, batch < min p.batch 31 ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ next : SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp 0 batch)
        shuffles (votes + 1) ends,
        WarpFollowsEvent l X g cur.pos src index target →
          WarpFollowsEvent l X g next.pos src index target := by
  have hAll := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.min_le_left p.batch 31))
  obtain ⟨batch, ⟨hb, hLo, hHi⟩, _⟩ := tileBatch_existsUnique p (hCta.trans_le hAll)
  have hIn : batch < min p.batch 31 := by
    by_contra! h
    exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_right p.heads (tilePrefix_mono p h)).trans hLo)) hCta
  have hGroup : batch < 31 := hIn.trans_le (Nat.min_le_right ..)
  have hReadyExists : ∃ ready : SchedulerWarpAt l X g 297 (fun lane =>
      (89, .pred (decide (0 + lane < batch))) :: (1079, b32 (tilePrefix p 0 * p.heads)) ::
        loaderVoteCarry p l g warp 0 lane) shuffles votes ends, ready.pos = cur.pos := by
    have hReady := loaderFirstBallotReadyAt hp hg hGroup hb hLo hHi cur
    rw [← firstBallotFacts_eq p l g warp batch] at hReady
    exact hReady
  obtain ⟨ready, hPos⟩ := hReadyExists
  have hAdvance : WarpFollowsEvent l X g cur.pos src index target →
      WarpFollowsEvent l X g ready.pos src index target := fun h => hPos.symm ▸ h
  obtain ⟨chosen, hChosen⟩ := loaderSelectBatchTo hp hX hg (Nat.zero_le batch)
    (by omega) hb ready (hProgress.imp_right hAdvance) hPc
  exact ⟨batch, hIn, hLo, hHi, chosen, hChosen ∘ hAdvance⟩

/-- The first group's selected batch on a terminated trace. -/
theorem loaderFirstBatch {g warp shuffles votes : Nat} (hg : g < l.threads)
    (hCta : g / l.block < tilePrefix p (min p.batch 31) * p.heads)
    (cur : SchedulerWarpAt l X g 288 (loaderFirstRouteFacts p l g warp) shuffles votes) :
    ∃ batch, batch < min p.batch 31 ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      Nonempty (SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp 0 batch)
        shuffles (votes + 1)) := by
  obtain ⟨batch, hIn, hLo, hHi, next, _⟩ := loaderFirstBatchTo hp hX hg hCta cur
    (src := 0) (index := 0) (target := ⟨298, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨batch, hIn, hLo, hHi, ⟨next⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

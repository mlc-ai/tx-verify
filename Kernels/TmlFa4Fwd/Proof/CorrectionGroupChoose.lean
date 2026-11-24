-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFirstRoute
public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations
import Kernels.TmlFa4Fwd.Flow.Code.Part122
import Kernels.TmlFa4Fwd.Flow.Code.Part123
import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.WarpVoteProgress
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem groupCoreCode :
    ((kernel.code.drop 7864).take 23).all (fun i => Assumptions.coreOp i.op) = true := by
  kernel_rfl

theorem groupCoreOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 7864 ≤ t.pc) (hHi : t.pc < 7887) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 7864).take 23 := by
      apply List.mem_of_getElem? (i := t.pc - 7864)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp groupCoreCode _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

theorem groupLinear {l : Launch} {g pc n : Nat} {t u : TState} {regs : List Nat}
    (hLo : 7864 ≤ pc) (hHi : pc + n ≤ 7887) (ht : t.pc = pc)
    (hWrites : ((kernel.code.drop pc).take n).all
      (fun i => regs.all (fun r => !(writesRegs i.op).contains r)) = true)
    (hFallthrough : ((kernel.code.drop pc).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧ ∀ r ∈ regs, u.regs r = t.regs r := by
  have hlo : pc ≤ t.pc := ht.ge
  have hhi : t.pc + n ≤ pc + n := by rw [ht]
  exact ⟨schedulerLocalTransport hFallthrough
    (fun ha hb => groupCoreOut (by omega) (by omega)) hr hlo hhi,
    fun _ h => schedulerLocalFrame hWrites hFallthrough hr hlo hhi h⟩

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The decoded ballot comparison marks precisely the lanes preceding the selected batch. -/
private theorem correctionGroupBallot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {first batch lane cta : Nat} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch) (hLane : lane < 32)
    (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 4 7869
      [(7272, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
       (7271, b32 (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i)),
       (7274, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
       (7142, b32 p.heads), (1618, b32 cta)] 7873
      [(1623, b32 (tilePrefix p first * p.heads)),
       (710, .pred (decide (first + lane < batch)))] := by
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
  change At t 7869
    [(7272, b32 total), (7271, b32 part), (7274, b32 tail), (7142, b32 p.heads), (1618, b32 cta)]
    at ht
  change ∃ u, run kernel [] l g 4 t = some u ∧
    At u 7873 [(1623, b32 start), (710, .pred (decide (first + lane < batch)))]
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

private theorem correctionGroupVote {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hit : Bool)
    (hpc : t.pc = 7873) (hf : t.fault = none) (hv : t.regs 710 = some (.pred hit)) :
    out kernel [] l g t = .ev (.vote (2 ^ 32 - 1) hit
      (fun mask => next (setReg t 5913 (b32 mask.toNat)))) := by
  rw [out_event hf (by rw [hpc]; exact Flow.code_7873) rfl rfl]
  change Out.ev (voteTmpl l g t 5913 710 false (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [voteTmpl, readPred, readReg, hv, hBlock, bind, Except.bind, pure, Except.pure, b32]
  rfl

private theorem correctionGroupPopcount (l : Launch) (g : Nat) {first n : Nat}
    (hn : n < 32) (hbound : first + n < 2 ^ 31) :
    Seg kernel [] l g 4 7874 [(5913, b32 (2 ^ n - 1)), (7273, b32 first)] 7878
      [(1624, b32 n), (7277, b32 (first + n)), (711, .pred (decide (n = 0))),
       (7275, b32 0)] := by
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

/-- A nonexhausted correction group sets the default coordinates and falls through to the ballot. -/
private theorem correctionGroupAvailable (l : Launch) (g : Nat) {first batch : Nat}
    (hGroup : first < batch) (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 5 7864 [(7273, b32 first), (7277, b32 batch)] 7869
      [(784, .pred false), (9605, b64 0), (7276, b32 0)] := by
  intro t ht
  have hf : first < 2 ^ 31 := by omega
  obtain ⟨u, hu, hU⟩ : ∃ u, run kernel [] l g 4 t = some u ∧
      At u 7868 [(709, .pred false), (784, .pred false), (9605, b64 0), (7276, b32 0)] := by
    seg_fp ht using
      first
      | rfl
      | simp only [compare, Option.getD_some, truncBits_ofNat (show first < 2 ^ 32 by omega)
          (by decide), truncBits_ofNat (show batch < 2 ^ 32 by omega) (by decide),
          signedWord hf, signedWord hBatch, ge_iff_le, Int.ofNat_le,
          decide_eq_false (Nat.not_le_of_lt hGroup)]
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7868 false hU hU.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hu hv, hV.mono hV.2.2.2.2.2⟩

/-- Registers carried from the selected request-group prefix through its ballot. -/
def correctionGroupABI (p : Params) (l : Launch) (g lane : Nat) : List (Nat × Value) :=
  (1618, b32 (g / l.block)) :: firstShuffleFacts p l (warpLane l g lane)

def correctionGroupEntry (p : Params) (l : Launch) (g first lane : Nat) : List (Nat × Value) :=
  [(7274, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)), (7273, b32 first),
    (7272, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
    (7271, b32 (prefixWindow (groupLaneTiles p first) 32 lane)),
    (7270, b32 (groupLaneTiles p first lane)), (7142, b32 p.heads)] ++
  correctionGroupABI p l g lane

def correctionVoteCarry (p : Params) (l : Launch) (g first lane : Nat) :
    List (Nat × Value) :=
  [(9605, b64 0), (7276, b32 0), (784, .pred false),
    (7273, b32 first), (7270, b32 (groupLaneTiles p first lane)),
    (7271, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7142, b32 p.heads)] ++ correctionGroupABI p l g lane

def correctionChosenFacts (p : Params) (l : Launch) (g first batch lane : Nat) :
    List (Nat × Value) :=
  [(1624, b32 (batch - first)), (7277, b32 batch), (711, .pred (decide (batch = first))),
    (7275, b32 0), (1623, b32 (tilePrefix p first * p.heads))] ++
  (correctionVoteCarry p l g first lane).filter (fun pair => pair.1 != 7277)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g first batch shuffles votes : Nat} (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
include hp hFirst hGroup hBatch hLo hHi

/-- A nonexhausted group reaches the actual selection ballot with the mathematically
selected request's lane comparison. -/
theorem correctionGroupBallotReadyPreserving {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7864 (correctionGroupEntry p l g first) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 7873 (fun lane =>
      (710, .pred (decide (first + lane < batch))) :: (1623, b32 (tilePrefix p first * p.heads)) ::
        correctionVoteCarry p l g first lane) shuffles votes ends,
      next.pos = cur.pos ∧ next.before = cur.before := by
  let cta := g / l.block
  have hf : first < p.batch := hFirst.trans_lt hBatch
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let keep := (correctionGroupEntry p l g first lane).map Prod.fst
  have ht := cur.checkpoint lane hl
  have hFact := ht.2.2.2.2
  have hAbi : Holds (cur.state lane).regs (correctionGroupABI p l g lane) :=
    hFact.2.2.2.2.2.2
  have hBatchWord := holds_lookup hAbi (show (correctionGroupABI p l g lane).lookup 7277 =
      some (b32 p.batch) from rfl)
  have hAvailable : At (cur.state lane) 7864 [(7273, b32 first), (7277, b32 p.batch)] :=
    ht.mono ⟨hFact.2.1, hBatchWord, trivial⟩
  obtain ⟨u, hu, hU⟩ := correctionGroupAvailable l thread hf hp.shape.2.1 _ hAvailable
  obtain ⟨huA, huFrame⟩ := groupLinear (regs := keep) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hSave := holdsSchedulerFrame hFact huFrame (fun _ h => List.mem_map_of_mem h)
  have hHead : u.regs 7142 = some (b32 p.heads) := hSave.2.2.2.2.2.1
  have hCta : u.regs 1618 = some (b32 cta) := hSave.2.2.2.2.2.2.1
  have hTotal : u.regs 7272 = some (b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)) :=
    hSave.2.2.1
  have hPart := hSave.2.2.2.1
  change u.regs 7271 = some (b32 (prefixWindow (groupLaneTiles p first) 32 lane)) at hPart
  rw [prefixWindow_warp _ hl] at hPart
  have hCount : u.regs 7270 = some (b32 (groupLaneTiles p first lane)) :=
    hSave.2.2.2.2.1
  obtain ⟨v, hv, hV⟩ := correctionGroupBallot hp thread hFirst hGroup
    hBatch hl hLo hHi u (hU.mono ⟨hTotal, hPart, hSave.1, hHead, hCta, trivial⟩)
  let carry := correctionVoteCarry p l g first lane
  let regs := carry.map Prod.fst
  have hCarry : Holds u.regs carry :=
    ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.2.2.1, hU.2.2.2.2.1,
      hSave.2.1, hCount, hPart, hHead, hSave.2.2.2.2.2.2⟩
  obtain ⟨hvA, hvFrame⟩ := groupLinear (regs := regs) (by decide) (by decide) hU.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hSaved := holdsSchedulerFrame hCarry hvFrame (fun _ h => List.mem_map_of_mem h)
  exact ⟨v, run_rtg (run_comp huA hvA),
    hV.mono ⟨hV.2.2.2.2.2.1, hV.2.2.2.2.1, hSaved⟩⟩

/-- Prepare the selected group ballot without advancing any event cursor. -/
theorem correctionGroupBallotReadyAt {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7864 (correctionGroupEntry p l g first) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 7873 (fun lane =>
      (710, .pred (decide (first + lane < batch))) :: (1623, b32 (tilePrefix p first * p.heads)) ::
        correctionVoteCarry p l g first lane) shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ :=
    correctionGroupBallotReadyPreserving hp hFirst hGroup hBatch hLo hHi cur
  exact ⟨next,hPos⟩

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem correctionGroupVoteNext {g first batch shuffles votes : Nat}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7873 (fun lane =>
      (710,.pred (decide (first+lane < batch))) :: (1623,b32 (tilePrefix p first*p.heads)) ::
        correctionVoteCarry p l g first lane) shuffles votes ends) {lane : Nat} (hl : lane < 32) :
    Next kernel Assumptions.all l (warpLane l g lane) (cur.before lane) (cur.state lane)
      (.vote (2^32-1) (decide (first+lane < batch))
        (fun word => next (setReg (cur.state lane) 5913 (b32 word.toNat)))) := by
  have ht := cur.checkpoint lane hl
  have hOut := correctionGroupVote hp (warpLane l g lane) (cur.state lane)
    (decide (first+lane < batch)) ht.1 ht.2.2.2.1 ht.2.2.2.2.1
  exact ⟨cur.localSteps lane hl, (groupCoreOut (by rw [ht.1]; decide)
    (by rw [ht.1]; decide)).trans hOut⟩

/-- Consume each present group-selection vote and replay its returned mask through the decoded
popcount, preserving the common collective ordinal of the warp. -/
private theorem correctionSelectBatchPresent (hX : Consistent l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7873 (fun lane =>
      (710, .pred (decide (first + lane < batch))) ::
        (1623, b32 (tilePrefix p first * p.heads)) ::
        correctionVoteCarry p l g first lane) shuffles votes ends)
    (hSuffix : ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ []) :
    ∃ next : SchedulerWarpAt l X g 7878 (correctionChosenFacts p l g first batch)
        shuffles (votes + 1) ends, next.pos = (fun lane => cur.pos lane+1) ∧
      ∀ lane < 32, ∃ word,
        X.get (warpLane l g lane,cur.pos lane) =
          some ⟨7873,.vote (2^32-1) (decide (first+lane < batch)) word⟩ ∧
        EStep kernel Assumptions.all l (warpLane l g lane) (cur.state lane)
          ⟨7873,.vote (2^32-1) (decide (first+lane < batch)) word⟩ (some (next.before lane)) := by
  let thread := warpLane l g
  let hit := fun lane => decide (first + lane < batch)
  let after := fun (lane : Nat) (word : BitVec 32) =>
    next (setReg (cur.state lane) 5913 (b32 word.toNat))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hNext (lane : Nat) (hl : lane < 32) := correctionGroupVoteNext hp cur hl
  have hVote (lane : Nat) : ∃ word, lane < 32 →
      X.get (thread lane, cur.pos lane) = some ⟨7873, .vote (2 ^ 32 - 1) (hit lane) word⟩ ∧
        Run kernel Assumptions.all l (thread lane) (after lane word)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨word, he, _, hr⟩ := (hNext lane hl).ballot_at_nonempty
        (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.vote lane hl)
      exact ⟨word, fun _ => ⟨by rw [(cur.checkpoint lane hl).1] at he; exact he, hr⟩⟩
    · exact ⟨0, fun h => (hl h).elim⟩
  choose word obs using hVote
  obtain ⟨hOrdinal, _, hOrd⟩ := cur.ordinals.ballot (fun _ => 7873) hit word
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
        At v 7878 (correctionChosenFacts p l g first batch lane) := by
    by_cases hl : lane < 32
    · have hLane : laneOf l (thread lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hPeers (j : Nat) (hj : j < 32) : ∃ k val,
          let e := (thread lane - laneOf l (thread lane) + j, k)
          X.get e = some ⟨7873, .vote (2 ^ 32 - 1) (hit j) val⟩ ∧
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
          (710, .pred (hit lane)) :: (1623, b32 (tilePrefix p first * p.heads)) ::
            correctionVoteCarry p l g first lane) : pair.1 ≠ 5913 := by
        intro he
        have hm' := List.mem_map_of_mem (f := Prod.fst) hm
        rw [he] at hm'
        exact (of_decide_eq_true rfl : 5913 ∉
          710 :: 1623 :: (correctionVoteCarry p l g first lane).map Prod.fst) hm'
      have ha := ht.set (v := b32 (word lane).toNat) hFresh
      have hChosen : At (after lane (word lane)) 7874
          [(5913, b32 (2 ^ n - 1)), (7273, b32 first)] := by
        refine ha.mono ⟨?_, ha.2.2.2.2.2.2.2.2.2.2.1, trivial⟩
        rw [← hValue]
        exact ha.2.2.2.2.1
      let carry := (correctionVoteCarry p l g first lane).filter (fun pair => pair.1 != 7277)
      let frame := (1623, b32 (tilePrefix p first * p.heads)) :: carry
      let regs := frame.map Prod.fst
      have hCarry := ha.2.2.2.2.2.2.2
      have hKeep : Holds (after lane (word lane)).regs frame := by
        refine ⟨ha.2.2.2.2.2.2.1, ?_⟩
        have hFilter {F : List (Nat × Value)} (h : Holds (after lane (word lane)).regs F) :
            Holds (after lane (word lane)).regs (F.filter (fun pair => pair.1 != 7277)) := by
          induction F with
          | nil => trivial
          | cons a as ih =>
            rw [List.filter_cons]
            by_cases ha : (a.1 != 7277) = true
            · simp only [ha, ↓reduceIte]
              exact ⟨h.1, ih h.2⟩
            · simp only [ha]
              exact ih h.2
        exact hFilter hCarry
      obtain ⟨v, hv, hV⟩ := correctionGroupPopcount l (thread lane) hn hBound
        (after lane (word lane)) hChosen
      obtain ⟨hvA, hvFrame⟩ := groupLinear (regs := regs) (by decide) (by decide) hChosen.1
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hv
      have hSaved := holdsSchedulerFrame hKeep hvFrame (fun _ h => List.mem_map_of_mem h)
      have hZ : n = 0 ↔ batch = first := by dsimp [n]; omega
      exact ⟨v, fun _ => ⟨run_rtg hvA, hV.mono
        ⟨hV.2.2.2.2.1, by simpa only [hnAdd] using hV.2.2.2.2.2.1,
        by simpa only [hZ] using hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.1, hSaved⟩⟩⟩
    · exact ⟨after lane (word lane), fun h => (hl h).elim⟩
  choose state h using hLocal
  refine ⟨⟨pos,fun lane => after lane (word lane),state,hOrd,
    fun lane hl => (obs lane hl).2,fun lane hl => (h lane hl).1,fun lane hl => (h lane hl).2⟩,
    rfl,fun lane hl => ⟨word lane,(obs lane hl).1,_,(hNext lane hl).stop,word lane,?_,rfl⟩⟩
  rw [(cur.checkpoint lane hl).1]

/-- Consume each actual PC 7873 vote and replay its returned mask through the decoded
popcount, preserving the common collective ordinal of the warp. -/
theorem correctionSelectBatchTo (hX : Consistent l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch) {ends : Nat → Option TState}
    {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 7873 (fun lane =>
      (710, .pred (decide (first + lane < batch))) ::
        (1623, b32 (tilePrefix p first * p.heads)) ::
        correctionVoteCarry p l g first lane) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hTarget : 7873 < target.pc) :
    ∃ next : SchedulerWarpAt l X g 7878 (correctionChosenFacts p l g first batch)
        shuffles (votes + 1) ends, WarpFollowsEvent l X g cur.pos src index target →
          WarpFollowsEvent l X g next.pos src index target := by
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hNext (lane : Nat) (hl : lane < 32) := correctionGroupVoteNext hp cur hl
  have hSuffix : ∀ lane < 32, (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with h | h
    · intro lane hl hNil
      have hRun := cur.continuation lane hl
      rw [hNil, h lane hl] at hRun
      cases hRun
    · exact h.ballotSuffix hX cur.ordinals hBlock hg (hNext src h.lane)
        (cur.continuation src h.lane)
  obtain ⟨next,hPos,hObserved⟩ :=
    correctionSelectBatchPresent hp hX hg hFirst hGroup hBatch cur hSuffix
  refine ⟨next,fun h => ?_⟩
  rw [hPos]
  apply h.afterCommonEvent hX hBlock hg hTarget
  intro lane hl
  obtain ⟨_,he,_⟩ := hObserved lane hl
  exact ⟨_,he,rfl,by intro he; cases he⟩

/-- The selected correction group performs its full-warp request ballot in a maximal trace. -/
theorem correctionSelectBatchOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ batch)
    (hGroup : batch < first+31) (hBatch : batch < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7873 (fun lane =>
      (710,.pred (decide (first+lane < batch))) ::
        (1623,b32 (tilePrefix p first*p.heads)) ::
          correctionVoteCarry p l g first lane) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7878 (correctionChosenFacts p l g first batch)
      shuffles (votes+1) ends) := by
  let thread := warpLane l g
  let hit := fun lane => decide (first+lane < batch)
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame (lane : Nat) (hl : lane < 32) := Step.sameWarp_lane hBlock hg hl
  have hSuffix (lane : Nat) (hl : lane < 32) : (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    have reach (h : Nat) (hs : SameWarp l (thread lane) h) : SameWarp l g h :=
      Step.sameWarp_trans (hSame lane hl).1 hs
    obtain ⟨_,he,_⟩ := Step.ballot_occurs_of_maximal hMax hBlock (hSame lane hl).1.1.2.1
      (pc := 7873) (ordinal := votes) (mask := 2^32-1)
      (cur.pos ∘ laneOf l) (hit ∘ laneOf l)
      (fun h _ => by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true (Nat.mod_lt _ (by decide)))
      (fun h hs => by
        rw [← Step.warpLane_of_sameWarp (reach h hs)]
        exact .inl (List.ne_nil_of_length_pos
          ((cur.positive _ (Nat.mod_lt _ (by decide))).trans_le
            (cur.bounded _ (Nat.mod_lt _ (by decide))))))
      (fun h hs => by
        let k := laneOf l h
        have hk : k < 32 := Nat.mod_lt _ (by decide)
        have hEq : warpLane l g k = h := Step.warpLane_of_sameWarp (reach h hs)
        let dest (word : BitVec 32) := next (setReg (cur.state k) 5913 (b32 word.toNat))
        refine ⟨cur.before k,cur.state k,ends k,dest,?_,?_,?_,(cur.checkpoint k hk).1,?_,?_,?_⟩
        · simpa only [Function.comp_apply,hEq] using cur.bounded k hk
        · change ((X.tr h).take (cur.pos k)).countP isFullWarpVote = votes
          rw [← hEq]
          exact cur.ordinals.vote k hk
        · simpa only [Function.comp_apply,hEq] using cur.released k hk
        · simpa only [Function.comp_apply,hEq] using cur.recorded k hk
        · simpa only [Function.comp_apply,hEq] using cur.continuation k hk
        · have hn := correctionGroupVoteNext hp cur.toSchedulerWarpAt hk
          simpa only [Function.comp_apply,hEq,dest] using hn)
      (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes h))
    have hLen := len_of_get he
    rw [Function.comp_apply,(hSame lane hl).2] at hLen
    exact fun hNil => (Nat.not_le_of_gt hLen) (List.drop_eq_nil_iff.mp hNil)
  obtain ⟨next,hPos,hObserved⟩ :=
    correctionSelectBatchPresent hp hMax.1 hg hFirst hGroup hBatch cur.toSchedulerWarpAt hSuffix
  refine ⟨⟨next,?_,?_,?_,?_⟩⟩
  · intro lane hl
    rw [hPos]
    exact Nat.succ_pos _
  · intro lane hl
    rw [hPos]
    obtain ⟨_,he,_⟩ := hObserved lane hl
    exact len_of_get he
  · intro lane hl hLast
    refine ⟨fun _ _ _ _ => ?_⟩
    rw [hPos] at hLast
    change cur.pos lane+1 = (X.tr (thread lane)).length at hLast
    have hId : (X.tr (thread lane)).length-1 = cur.pos lane := by omega
    rw [hId]
    obtain ⟨_,he,_⟩ := hObserved lane hl
    exact hMax.1.dependency.ready _
      (by simp [Returned,he,Kind.resume])
  · intro lane hl
    rw [hPos,List.take_add_one]
    obtain ⟨_,he,hStep⟩ := hObserved lane hl
    rw [show (X.tr (thread lane))[cur.pos lane]? = _ from he]
    exact (cur.recorded lane hl).snoc (cur.localSteps lane hl) hStep

/-- The first scanned group chooses its actual batch whenever its CTA lies in that group. -/
theorem correctionFirstBatchTo (hX : Consistent l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads)
    (hCta : g / l.block < tilePrefix p (min p.batch 31) * p.heads) {ends : Nat → Option TState}
    {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 7864 (correctionFirstRouteFacts p l g) shuffles votes ends)
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hTarget : 7873 < target.pc) :
    ∃ batch, batch < min p.batch 31 ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ next : SchedulerWarpAt l X g 7878 (correctionChosenFacts p l g 0 batch)
        shuffles (votes + 1) ends, WarpFollowsEvent l X g cur.pos src index target →
          WarpFollowsEvent l X g next.pos src index target := by
  have hAll := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.min_le_left p.batch 31))
  obtain ⟨batch, ⟨hb, hLo, hHi⟩, _⟩ := tileBatch_existsUnique p (hCta.trans_le hAll)
  have hIn : batch < min p.batch 31 := by
    by_contra! h
    exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_right p.heads (tilePrefix_mono p h)).trans hLo)) hCta
  have hGroup : batch < 0 + 31 := hIn.trans_le (Nat.min_le_right ..)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨entry, hEntry⟩ : ∃ entry : SchedulerWarpAt l X g 7864
      (correctionGroupEntry p l g 0) shuffles votes ends, entry.pos = cur.pos := by
    apply cur.advanceLocalAt
    intro lane hl
    have ht := cur.checkpoint lane hl
    have hR := ht.2.2.2.2
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hSum := groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    have he : (∑ i ∈ Finset.range 32, groupLaneTiles p 0 i) = tilePrefix p (min p.batch 31) :=
      by simpa [tilePrefix] using hSum
    have hTotal := hR.2.2.2.1
    rw [← he] at hTotal
    have hTiles := hR.2.2.2.2.2.1
    rw [hLane] at hTiles
    exact ⟨_, .refl, ht.mono ⟨hR.1, hR.2.1, hTotal, hR.2.2.2.2.1, hTiles,
      hR.2.2.2.2.2.2.1, hR.2.2.1, hR.2.2.2.2.2.2.2.2⟩⟩
  obtain ⟨ready, hReady⟩ :=
    correctionGroupBallotReadyAt hp (Nat.zero_le batch) hGroup hb hLo hHi entry
  have hPos := hReady.trans hEntry
  obtain ⟨chosen, hChosen⟩ := correctionSelectBatchTo hp hX hg (Nat.zero_le batch) hGroup hb
    ready (by rw [hPos]; exact hProgress) hTarget
  exact ⟨batch, hIn, hLo, hHi, chosen, fun h => hChosen (hPos.symm ▸ h)⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction

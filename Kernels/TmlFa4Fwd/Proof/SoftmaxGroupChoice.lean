-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackSearch
import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations

import Lemmas.Step.WarpVoteProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

def groupVoteCarry (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) (first : Nat) :=
  [(1221, b32 (tilePrefix p first * p.heads)), (783, Value.pred false), (7246, b32 0)] ++
    groupRouteFacts p l g warp first

private def groupVoteFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (first batch : Nat) :=
  (466, Value.pred (decide (first + laneOf l g < batch))) :: groupVoteCarry p l g warp first

/-- The ballot result records the selected batch and retains its group's prefix and tile words. -/
def selectedGroupFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) (first batch : Nat) :=
  [(1222, b32 (batch - first)), (7247, b32 batch), (2727, b32 (2 ^ (batch - first) - 1))] ++
    (groupVoteCarry p l g warp first).filter (fun pair => pair.1 != 7247)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem groupBallotReadyPreserving (hp : Pre p l m) {g first batch shuffles votes : Nat}
    {warp : Fin 8} (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3212 (fun lane =>
      groupRouteFacts p l (warpLane l g lane) warp first) shuffles votes ends) :
    ∃ u : SchedulerWarpAt l X g 3220 (fun lane =>
      groupVoteFacts p l (warpLane l g lane) warp first batch) shuffles votes ends,
      u.pos = cur.pos ∧ u.before = cur.before := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  apply cur.advanceLocalPreserving
  intro lane hl
  let t := warpLane l g lane
  let F := groupRouteFacts p l t warp first
  have ht := cur.checkpoint lane hl
  have hs : At (cur.state lane) 3212 [(7243, b32 first), (7247, b32 p.batch)] :=
    ht.mono ⟨ht.2.2.2.2.2.1, holds_lookup ht.2.2.2.2 rfl, trivial⟩
  obtain ⟨v, hv, hV⟩ := (firstGroupAvailable l t (by omega) hp.shape.2.1).apply hs
  obtain ⟨hvA, hvFrame⟩ := selectionLocal (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hF : Holds v.regs F := holdsSchedulerFrame ht.2.2.2.2 hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  have hLane : laneOf l t = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hCta : t / l.block = g / l.block := (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
  have hCtaWord : v.regs 1072 = some (b32 (g / l.block)) := by
    rw [← hCta]
    exact holds_lookup hF rfl
  have hPart := hF.2.2.2.1
  change v.regs 7241 = some (b32 (∑ i ∈ Finset.range (laneOf l t + 1),
    groupLaneTiles p first i)) at hPart
  rw [hLane] at hPart
  obtain ⟨u, hu, hU⟩ := (groupBallotSegment hp t hFirst hGroup hb hl hLo hHi).apply
    (hV.mono ⟨hF.2.2.1, hPart, hF.1, holds_lookup hF (show F.lookup 7140 = _ from rfl),
      hCtaWord, trivial⟩)
  let keep := [(783, Value.pred false), (7246, b32 0)] ++ F
  have hKeep : Holds v.regs keep := ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hF⟩
  obtain ⟨huA, huFrame⟩ := selectionLocal (regs := keep.map Prod.fst) (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hSaved := holdsSchedulerFrame hKeep huFrame (fun _ hm => List.mem_map_of_mem hm)
  refine ⟨u, run_rtg (run_comp hvA huA), hU.mono ?_⟩
  change u.regs 466 = some (.pred (decide (first + laneOf l t < batch))) ∧ _
  rw [hLane]
  exact ⟨hU.2.2.2.2.2.1, hU.2.2.2.2.1, hSaved⟩

private theorem groupBallotReady (hp : Pre p l m) {g first batch shuffles votes : Nat}
    {warp : Fin 8} (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3212 (fun lane =>
      groupRouteFacts p l (warpLane l g lane) warp first) shuffles votes ends) :
    ∃ u : SchedulerWarpAt l X g 3220 (fun lane =>
      groupVoteFacts p l (warpLane l g lane) warp first batch) shuffles votes ends,
      u.pos = cur.pos := by
  obtain ⟨u,hPos,_⟩ := groupBallotReadyPreserving hp hg hFirst hGroup hb hLo hHi cur
  exact ⟨u,hPos⟩

private theorem warpGroupChoiceOfPresent (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g first batch shuffles votes : Nat}
    {warp : Fin 8} (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hb : batch < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3220 (fun lane =>
      groupVoteFacts p l (warpLane l g lane) warp first batch) shuffles votes ends)
    (hSuffix : ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ []) :
    ∃ u : SchedulerWarpAt l X g 3223 (fun lane =>
      selectedGroupFacts p l (warpLane l g lane) warp first batch) shuffles (votes + 1) ends,
      ∃ words : Nat → BitVec 32,
        u.pos = (fun lane => cur.pos lane + 1) ∧
        u.before = (fun lane => next (setReg (cur.state lane) 2727 (b32 (words lane).toNat))) ∧
        ∀ lane < 32, X.get (warpLane l g lane,cur.pos lane) =
          some ⟨3220,.vote (2^32-1) (decide (first + lane < batch)) (words lane)⟩ := by
  let t := warpLane l g
  let hit := fun lane => decide (first + lane < batch)
  let digit := batch - first
  let mask := 2 ^ digit - 1
  let after := fun (lane : Nat) (word : BitVec 32) =>
    next (setReg (cur.state lane) 2727 (b32 word.toNat))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (t lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel Assumptions.all l (t lane) (cur.before lane) (cur.state lane)
        (.vote (2 ^ 32 - 1) (hit lane) (after lane)) := by
    have ht := cur.checkpoint lane hl
    have hPred := ht.2.2.2.2.1
    change (cur.state lane).regs 466 = some (.pred (decide (first + laneOf l (t lane) < batch)))
      at hPred
    rw [hLane lane hl] at hPred
    exact ⟨cur.localSteps lane hl, (selectionOut (by rw [ht.1]; decide)
      (by rw [ht.1]; decide)).trans (groupVoteOut hp _ _ _ ht.1 ht.2.2.2.1 hPred)⟩
  have hObs (lane : Nat) (hl : lane < 32) : ∃ word,
      X.get (t lane, cur.pos lane) = some ⟨3220, .vote (2 ^ 32 - 1) (hit lane) word⟩ ∧
      Run kernel Assumptions.all l (t lane) (after lane word)
        ((X.tr (t lane)).drop (cur.pos lane + 1)) (ends lane) := by
    obtain ⟨word, he, _, hr⟩ := (hNext lane hl).ballot_at_nonempty
      (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.vote lane hl)
    exact ⟨word, by rw [(cur.checkpoint lane hl).1] at he; exact he, hr⟩
  choose! word obs hRuns using hObs
  obtain ⟨hOrdinal, _, hOrd⟩ := cur.ordinals.ballot (fun _ => 3220) hit word obs
  have hLocal (lane : Nat) (hl : lane < 32) : ∃ v,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (t lane)) (after lane (word lane)) v ∧
      At v 3223 (selectedGroupFacts p l (t lane) warp first batch) := by
    have hPeers (j : Nat) (hj : j < 32) : ∃ k val,
        let e := (t lane - laneOf l (t lane) + j,k)
        X.get e = some ⟨3220, .vote (2 ^ 32 - 1) (hit j) val⟩ ∧
        X.MaskK voteClass e (2 ^ 32 - 1) votes := by
      refine ⟨cur.pos j, word j, ?_⟩
      dsimp only
      have eq : t lane - laneOf l (t lane) + j = t j := by
        rw [hLane lane hl]
        simp only [t, warpLane]
        omega
      rw [eq]
      exact ⟨obs j hj, hOrdinal j hj⟩
    have hWord := selectedGroupMask hX hFirst (obs lane hl) (hOrdinal lane hl) hPeers
    have hMask : (word lane).toNat = mask := by
      rw [hWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      exact lt_of_le_of_lt (Nat.sub_le ..) (Nat.pow_lt_pow_right (by decide) (by omega))
    have ht := cur.checkpoint lane hl
    have hFresh : ∀ x ∈ groupVoteFacts p l (t lane) warp first batch, x.1 ≠ 2727 :=
      of_decide_eq_true rfl
    have hAfter := ht.set (v := b32 (word lane).toNat) hFresh
    let F := groupVoteCarry p l (t lane) warp first
    have hF : Holds (after lane (word lane)).regs F := hAfter.2.2.2.2.2.2
    have hChosen : At (after lane (word lane)) 3221 [(2727, b32 mask), (7243, b32 first)] :=
      hAfter.mono ⟨hMask ▸ hAfter.2.2.2.2.1,
        holds_lookup hF (show F.lookup 7243 = _ from rfl), trivial⟩
    let hKeep := List.filter (fun pair => pair.1 != 7247) F
    let carry := (2727, b32 mask) :: hKeep
    have hFiltered {F : List (Nat × Value)} (h : Holds (after lane (word lane)).regs F) :
        Holds (after lane (word lane)).regs (F.filter (fun pair => pair.1 != 7247)) := by
      induction F with
      | nil => trivial
      | cons a as ih =>
        rw [List.filter_cons]
        by_cases ha : (a.1 != 7247) = true
        · simp only [ha, ↓reduceIte]
          exact ⟨h.1, ih h.2⟩
        · simp only [ha]
          exact ih h.2
    have hHold : Holds (after lane (word lane)).regs carry :=
      ⟨hChosen.2.2.2.2.1, hFiltered hF⟩
    have hAdd : first + digit = batch := Nat.add_sub_of_le hFirst
    have hb32 : first + digit < 2 ^ 32 := by rw [hAdd]; have := hp.shape.2.1; omega
    obtain ⟨v, hv, hV⟩ := (selectedBatchWord l (t lane) (n := digit) (by omega) hb32).apply hChosen
    obtain ⟨hvA, hvFrame⟩ := selectionLocal (regs := carry.map Prod.fst) (by decide) (by decide)
      hChosen.1 (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hv
    have hSaved := holdsSchedulerFrame hHold hvFrame (fun _ hm => List.mem_map_of_mem hm)
    exact ⟨v, run_rtg hvA, hV.mono ⟨hV.2.2.2.2.1, hAdd ▸ hV.2.2.2.2.2.1, hSaved⟩⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! state hLocalState hChosen using hLocal
  exact ⟨⟨fun lane => cur.pos lane+1, fun lane => after lane (word lane), state, hOrd,
    hRuns, hLocalState, hChosen⟩, word, rfl, rfl, obs⟩

private theorem warpGroupChoice (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hb : batch < p.batch)
    {ends : Nat → Option TState} {src index : Nat} {target : Event}
    (cur : SchedulerWarpAt l X g 3220 (fun lane =>
      groupVoteFacts p l (warpLane l g lane) warp first batch) shuffles votes ends)
    (hFollow : WarpFollowsEvent l X g cur.pos src index target) (hTarget : 3220 < target.pc) :
    ∃ u : SchedulerWarpAt l X g 3223 (fun lane =>
      selectedGroupFacts p l (warpLane l g lane) warp first batch) shuffles (votes + 1) ends,
      WarpFollowsEvent l X g u.pos src index target := by
  let t := warpLane l g
  let hit := fun lane => decide (first + lane < batch)
  let after := fun (lane : Nat) (word : BitVec 32) =>
    next (setReg (cur.state lane) 2727 (b32 word.toNat))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (t lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel Assumptions.all l (t lane) (cur.before lane) (cur.state lane)
        (.vote (2 ^ 32 - 1) (hit lane) (after lane)) := by
    have ht := cur.checkpoint lane hl
    have hPred := ht.2.2.2.2.1
    change (cur.state lane).regs 466 = some (.pred (decide (first + laneOf l (t lane) < batch)))
      at hPred
    rw [hLane lane hl] at hPred
    exact ⟨cur.localSteps lane hl, (selectionOut (by rw [ht.1]; decide)
      (by rw [ht.1]; decide)).trans (groupVoteOut hp _ _ _ ht.1 ht.2.2.2.1 hPred)⟩
  have hSuffix := hFollow.ballotSuffix hX cur.ordinals hBlock hg (hNext src hFollow.lane)
    (cur.continuation src hFollow.lane)
  obtain ⟨next,words,hPos,_,hEvents⟩ :=
    warpGroupChoiceOfPresent hp hX hg hFirst hGroup hb cur hSuffix
  refine ⟨next, ?_⟩
  rw [hPos]
  apply hFollow.afterCommonEvent hX hBlock hg hTarget
  exact fun lane hl => ⟨_, hEvents lane hl, rfl, by intro he; cases he⟩

/-- The selected scheduler group performs its actual request-selection ballot. -/
theorem groupChosenOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first batch shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first+31) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3212
      (fun lane => groupRouteFacts p l (warpLane l g lane) warp first) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 3223
      (fun lane => selectedGroupFacts p l (warpLane l g lane) warp first batch)
      shuffles (votes+1) ends) := by
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨prepared,hPos,hState⟩ :=
    groupBallotReadyPreserving hp hg hFirst hGroup hb hLo hHi cur.toSchedulerWarpAt
  let ready := cur.reframe prepared hPos hState
  let after := fun (lane : Nat) (word : BitVec 32) =>
    next (setReg (ready.state lane) 2727 (b32 word.toNat))
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (ready.state lane) =
        .ev (.vote (2^32-1) (decide (first + lane < batch)) (after lane)) := by
    have ht := ready.checkpoint lane hl
    have hPred := ht.2.2.2.2.1
    change (ready.state lane).regs 466 =
      some (.pred (decide (first + laneOf l (thread lane) < batch))) at hPred
    rw [show laneOf l (thread lane) = lane from (Step.sameWarp_lane hBlock hg hl).2] at hPred
    exact (selectionOut (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans
      (groupVoteOut hp _ _ _ ht.1 ht.2.2.2.1 hPred)
  have hPresent (lane : Nat) (hl : lane < 32) :
      (X.tr (thread lane)).drop (ready.pos lane) ≠ [] := by
    have hWarp := Step.sameWarp_lane hBlock hg hl
    have hActual := Step.ballot_occurs_of_maximal hMax hBlock hWarp.1.1.2.1
      (ready.pos ∘ laneOf l) (fun h => decide (first + laneOf l h < batch))
      (pc := 3220) (ordinal := votes) (mask := 2^32-1)
      (by
        intro peer _
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true (Nat.mod_lt _ (by decide)))
      (by
        intro peer hpWarp
        have hPeer := Step.sameWarp_trans hWarp.1 hpWarp
        have hEq := Step.warpLane_of_sameWarp hPeer
        rw [← hEq]
        apply Or.inl
        have hLane := Nat.mod_lt (peer % l.block) (by decide : 0 < 32)
        exact List.ne_nil_of_length_pos ((ready.positive _ hLane).trans_le (ready.bounded _ hLane)))
      (by
        intro peer hpWarp
        let k := laneOf l peer
        have hk : k < 32 := Nat.mod_lt _ (by decide)
        have hEq : warpLane l g (laneOf l peer) = peer :=
          Step.warpLane_of_sameWarp (Step.sameWarp_trans hWarp.1 hpWarp)
        refine ⟨ready.before k, ready.state k, ends k, after k, ?_, ?_, ?_,
          (ready.checkpoint k hk).1, ?_, ?_, ?_⟩
        · simpa only [Function.comp_apply,k,hEq] using ready.bounded k hk
        · change ((X.tr peer).take (ready.pos k)).countP isFullWarpVote = votes
          simpa only [k,hEq] using ready.ordinals.vote k hk
        · simpa only [Function.comp_apply,k,hEq] using ready.released k hk
        · simpa only [Function.comp_apply,k,hEq] using ready.recorded k hk
        · simpa only [Function.comp_apply,k,hEq] using ready.continuation k hk
        · have hNext : Next kernel Assumptions.all l (thread k) (ready.before k) (ready.state k)
              (.vote (2^32-1) (decide (first + k < batch)) (after k)) :=
            ⟨ready.localSteps k hk,hOut k hk⟩
          simpa only [Function.comp_apply,k,thread,hEq] using hNext)
      (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes h))
    obtain ⟨word,he,_⟩ := hActual
    change X.get (thread lane,ready.pos (laneOf l (thread lane))) = _ at he
    rw [hWarp.2] at he
    have hLen := len_of_get he
    change ready.pos (laneOf l (thread lane)) < (X.tr (thread lane)).length at hLen
    rw [show laneOf l (thread lane) = lane from hWarp.2] at hLen
    exact fun hn => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hn)
  obtain ⟨chosen,words,hChoice,hBefore,hEvents⟩ :=
    warpGroupChoiceOfPresent hp hMax.1 hg hFirst hGroup hb ready.toSchedulerWarpAt hPresent
  refine ⟨{ toSchedulerWarpAt := chosen
            positive := ?_, bounded := ?_, released := ?_, recorded := ?_ }⟩
  · rw [hChoice]
    intro lane _
    exact Nat.succ_pos _
  · rw [hChoice]
    exact fun lane hl => len_of_get (hEvents lane hl)
  · rw [hChoice]
    exact fun lane hl => releasedIfLast (hEvents lane hl) (by intro he; cases he)
  · intro lane hl
    have he := hEvents lane hl
    have hLen : ready.pos lane < (X.tr (thread lane)).length := len_of_get he
    rw [hChoice,hBefore,List.take_succ_eq_append_getElem hLen,
      (List.getElem?_eq_some_iff.mp he).2]
    exact (ready.recorded lane hl).snoc (ready.localSteps lane hl)
      ⟨_, hOut lane hl, words lane, by rw [(ready.checkpoint lane hl).1], rfl⟩

/-- Any active softmax CTA selects the unique batch containing its assigned tile. -/
theorem activeBatchOfEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index : Nat} {target : Event} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hSrc : src < 32) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hEvent : X.get (warpLane l g src,index) = some target) (hTarget : 3220 < target.pc) :
    let warp : Fin 8 := ⟨warpIndex l g, hWarp⟩
    ∃ first batch shuffles, first ≤ batch ∧ batch < first + 31 ∧ batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      ∃ (ends : Nat → Option TState) (cur : SchedulerWarpAt l X g 3223
        (fun lane => selectedGroupFacts p l (warpLane l g lane) warp first batch) shuffles 1 ends),
      WarpFollowsEvent l X g cur.pos src index target := by
  obtain ⟨batch, ⟨hb, hLo, hHi⟩, _⟩ := tileBatch_existsUnique p hWork
  obtain ⟨first, ord, hStart, hCutoff, ends, route, hRoute⟩ :=
    activeGroupOfEvent hp hX hg hWarp hSrc hWork hCuQ hEvent (by omega)
  have hFirst : first ≤ batch := by
    by_contra! h
    exact (Nat.not_le_of_lt hHi) ((Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p (show batch + 1 ≤ first by omega))).trans hStart)
  have hGroup : batch < first + 31 := by
    by_contra! h
    exact (Nat.not_le_of_lt hCutoff) ((Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p ((Nat.min_le_right _ _).trans h))).trans hLo)
  obtain ⟨ready, hReady⟩ := groupBallotReady hp hg hFirst hGroup hb hLo hHi route
  obtain ⟨selected, hSelected⟩ :=
    warpGroupChoice hp hX hg hFirst hGroup hb ready (hReady.symm ▸ hRoute) hTarget
  exact ⟨first, batch, ord, hFirst, hGroup, hb, hLo, hHi, ends, selected, hSelected⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax

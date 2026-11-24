-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainLaterScan
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTerminal
import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
import Kernels.TmlFa4Fwd.Flow.Code.Part042

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Allocation (drainRoots signedWord)

private theorem exhaustedDrainCutoff {p : Params} {l : Launch} {g : Nat} {t : TState}
    (hCta : g/l.block+1 < 2^31)
    (ht : At t 2747 ((7216,b32 (g/l.block+1))::
      (1072,b32 (g/l.block))::activeDrainExhaustedFrame p)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2750 (activeDrainExhaustedFrame p) := by
  let cta := g/l.block
  have hCta' : cta+1 < 2^31 := hCta
  have hSeg : Seg kernel [] l g 2 2747 [(7216,b32 (cta+1)),(1072,b32 cta)] 2749
      [(433,.pred false)] := by
    intro s hs
    seg_fp hs using simp only [compare,Option.getD_some,
      truncBits_ofNat (show cta < 2^32 by omega) (by decide),
      truncBits_ofNat (show cta+1 < 2^32 by omega) (by decide),
      signedWord (show cta < 2^31 by omega),signedWord hCta',Int.ofNat_le,
      decide_eq_false (show ¬cta+1 ≤ cta by omega)]
  obtain ⟨v,hv,hV⟩ := hSeg.apply (ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,trivial⟩)
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2749 false hV hV.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hRegs⟩ := activeDrainLocalKeep (ht.mono ht.2.2.2.2.2.2) (by decide) (by decide)
    (by change ((kernel.code.drop 2747).take 3).all
          (fun i => [7215,7149].all fun r => !(writesRegs i.op).contains r) = true
        decide +kernel) (by decide +kernel) (run_comp hv hu)
  exact ⟨u,hPath,hU.mono hRegs⟩

private theorem advanceDrainLoopLocal {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {t : TState} (ht : At t 2696 (activeDrainLoopFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      if p.batch ≤ first+31 then At u 2750 (activeDrainExhaustedFrame p)
      else At u 2701 ((1197,b32 (first+31))::activeDrainGroupFrame p l g (first+31)) := by
  let cta := g/l.block
  let limit := tilePrefix p (min p.batch (first+31))*p.heads
  let F := [(7210,b32 limit),(7139,b32 p.heads),(1180,b32 (laneOf l g)),(7506,b64 p.cuQBase)]
  have hBatch := hp.shape.2.1
  have hMargin := hp.shape.2.2.2.2.2
  have hBound : first+31 < 2^31 := by omega
  have hCta := (Nat.succ_le_of_lt (NamedBar.cta_lt hg)).trans_lt hp.grid.2.2
  have hx := ht.2.2.2.2
  have hAt : At t (scanSite .drain).head (groupScanFacts .drain first p.batch cta ++ F) :=
    ht.mono ⟨holds_lookup hx rfl,holds_lookup hx rfl,holds_lookup hx rfl,holds_lookup hx rfl,
      holds_lookup hx rfl,holds_lookup hx rfl,holds_lookup hx rfl,holds_lookup hx rfl,trivial⟩
  obtain ⟨u,hu,hU⟩ := advanceGroupScanPreserving (l := l) (g := g) (F := F) .drain hBound hBatch
    (by change ((kernel.code.drop 2696).take 5).all
          (fun i => [7210,7139,1180,7506].all fun r => !(writesRegs i.op).contains r) = true
        decide +kernel) hAt
  by_cases hMore : p.batch ≤ first+31
  · simp only [ite_eq_left hMore]
    rw [ite_eq_left hMore,Nat.min_eq_right hMore] at hU
    have hE : At u 2747 ((7216,b32 (cta+1))::(1072,b32 cta)::activeDrainExhaustedFrame p) :=
      hU.mono ⟨holds_lookup hU.2.2.2.2 rfl,holds_lookup hU.2.2.2.2 rfl,
        holds_lookup hU.2.2.2.2 rfl,holds_lookup hU.2.2.2.2 rfl,trivial⟩
    obtain ⟨v,hv,hV⟩ := exhaustedDrainCutoff (g := g) hCta hE
    exact ⟨v,(run_rtg hu).trans hv,hV⟩
  · simp only [ite_eq_right hMore]
    rw [ite_eq_right hMore,Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hMore))] at hU
    have hLimit : min p.batch (first+31) = first+31 :=
      Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hMore))
    have ho := hU.2.2.2.2
    have hF : u.regs 7210 = some (b32 (tilePrefix p (first+31)*p.heads)) := by
      have h := holds_lookup ho (r := 7210) (v := b32 limit) rfl
      simpa only [limit,hLimit] using h
    exact ⟨u,run_rtg hu,hU.mono ⟨holds_lookup ho rfl,holds_lookup ho rfl,holds_lookup ho rfl,hF,
      holds_lookup ho rfl,holds_lookup ho rfl,holds_lookup ho rfl,holds_lookup ho rfl,
      holds_lookup ho rfl,trivial⟩⟩

private theorem laterRouteLocal {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first : Nat} (hg : g < l.threads) (hf : first ≤ p.batch)
    {t : TState}
    (ht : At t 2746
      ([(7214,b32 (prefixWindow (groupLaneTiles p first) 32 31)),
        (7213,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l g))),
        (7212,b32 (groupLaneTiles p first (laneOf l g)))] ++ activeDrainGroupFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      if g/l.block < tilePrefix p (min p.batch (first+31))*p.heads then
        At u 2750 (activeDrainSelectedFrame p l g first)
      else At u 2696 (activeDrainLoopFrame p l g first) := by
  let cta := g/l.block
  let old := tilePrefix p first*p.heads
  let count := prefixWindow (groupLaneTiles p first) 32 31
  let cutoff := tilePrefix p (min p.batch (first+31))*p.heads
  let part := prefixWindow (groupLaneTiles p first) 32 (laneOf l g)
  let own := groupLaneTiles p first (laneOf l g)
  let F := [(7214,b32 count),(7213,b32 part),(7212,b32 own),(7215,b32 first),
    (1196,b32 (cta+1))] ++ activeDrainCommon p l g
  have hFit := hp.prefixWork_signed (Nat.min_le_left p.batch (first+31))
  change cutoff < 2^31 at hFit
  have hCount := hp.groupWindow_signed hf (show 31 < 32 by decide) 32
  change count < 2^31 at hCount
  have hOld : old < 2^31 := hp.prefixWork_signed hf
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hHead := hp.heads_signed
  have hSum : count*p.heads+old = cutoff := by
    have h := congrArg (· * p.heads) (groupTiles_eq p hf (by decide : 32 ≤ 32))
    rw [show count = ∑ i ∈ Finset.range 32, groupLaneTiles p first i from
      prefixWindow_warp _ (by decide)]
    simpa only [show min 31 32 = 31 by decide,Nat.add_mul,Nat.add_comm,cutoff,old] using h
  let more := decide (cutoff ≤ cta)
  have hSeg : Seg kernel [] l g 3 2746
      [(7214,b32 count),(7139,b32 p.heads),(7210,b32 old),(1072,b32 cta)] 2749
      [(433,.pred more),(7216,b32 cutoff),(7210,b32 cutoff)] := by
    intro s hs
    seg_fp hs using
      simp only [b32,← BitVec.ofNat_mul,← BitVec.ofNat_add,hSum,compare,Option.getD_some,
        truncBits_ofNat (show count < 2^32 by omega) (by decide),
        truncBits_ofNat (show p.heads < 2^32 by omega) (by decide),
        truncBits_ofNat (show old < 2^32 by omega) (by decide),
        truncBits_ofNat (show cutoff < 2^32 by omega) (by decide),
        truncBits_ofNat (show cta < 2^32 by omega) (by decide),
        signedWord hFit,signedWord hCta,Int.ofNat_le,more]
  have hRegs := ht.2.2.2.2
  obtain ⟨s,hs,hS⟩ := hSeg.apply
    (ht.mono ⟨holds_lookup hRegs rfl,holds_lookup hRegs rfl,holds_lookup hRegs rfl,
      holds_lookup hRegs rfl,trivial⟩)
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2749 more hS hS.2.2.2.2.1 (by simp)
  have hKeepAt : At t 2746 F := ht.mono ⟨hRegs.1,hRegs.2.1,hRegs.2.2.1,
    hRegs.2.2.2.1,hRegs.2.2.2.2.1,hRegs.2.2.2.2.2.2⟩
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep hKeepAt (by decide) (by decide) (by
    change ((kernel.code.drop 2746).take 4).all
      (fun i => [7214,7213,7212,7215,1196,7149,7139,1180,7506,1072].all
        fun r => !(writesRegs i.op).contains r) = true
    decide +kernel) (by decide +kernel) (run_comp hs hu)
  change ∃ u, _ ∧ if cta < cutoff then _ else _
  by_cases hSel : cta < cutoff
  · simp only [ite_eq_left hSel]
    have hPc : u.pc = 2750 := by simpa [more,Nat.not_le_of_lt hSel] using hU.1
    refine ⟨u,hPath,⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩⟩
    exact ⟨hKeep.2.2.1,hKeep.2.1,hKeep.1,hU.2.2.2.2.2.1,hKeep.2.2.2.1,
      hKeep.2.2.2.2.2⟩
  · simp only [ite_eq_right hSel]
    have hPc : u.pc = 2696 := by simpa [more,Nat.le_of_not_gt hSel] using hU.1
    exact ⟨u,hPath,⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,hKeep.2.2.2.1,hKeep.2.2.2.2.1,
      hU.2.2.2.2.2.2.1,hKeep.2.2.2.2.2⟩⟩

private theorem relinquishOfLoop {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {ends : Nat → Option TState} :
    ∀ fuel first shuffles, p.batch-first = fuel → first ≤ p.batch →
      tilePrefix p (min p.batch (first+31))*p.heads ≤ g/l.block →
      SchedulerWarpReached l X g 2696
        (fun lane => activeDrainLoopFrame p l (warpLane l g lane) first) shuffles votes ends →
      MmaRelinquishPrefix l X g := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first shuffles hFuel hf hlo cur
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    let nextFirst := first+31
    by_cases hStop : p.batch ≤ first+31
    · have hDone : Nonempty (SchedulerWarpReached l X g 2750
          (fun _ => activeDrainExhaustedFrame p) shuffles votes ends) := by
        apply cur.advanceLocal
        intro i hi
        have hLane := (Step.sameWarp_lane hBlock hg hi).1
        obtain ⟨u,hu,hU⟩ := advanceDrainLoopLocal hp hLane.1.2.1 hf (cur.checkpoint i hi)
        rw [ite_eq_left hStop] at hU
        exact ⟨u,hu,hU⟩
      obtain ⟨done⟩ := hDone
      exact activeDrainRelinquishOfExhausted hp hMax hg hw done
    · have hn : nextFirst < p.batch := Nat.lt_of_not_ge hStop
      have hAdvance : Nonempty (SchedulerWarpReached l X g 2701
          (fun i => (1197,b32 nextFirst)::activeDrainGroupFrame p l (warpLane l g i) nextFirst)
          shuffles votes ends) := by
        apply cur.advanceLocal
        intro i hi
        have hLane := (Step.sameWarp_lane hBlock hg hi).1
        obtain ⟨u,hu,hU⟩ := advanceDrainLoopLocal hp hLane.1.2.1 hf (cur.checkpoint i hi)
        rw [ite_eq_right hStop] at hU
        exact ⟨u,hu,hU⟩
      obtain ⟨entry⟩ := hAdvance
      obtain ⟨words⟩ := activeDrainLaterWordsOfMaximal hp hMax hCuQ hg hn.le entry
      obtain ⟨scan⟩ := activeDrainLaterScanOfMaximal hp hMax hg hn.le words
      let cutoff := tilePrefix p (min p.batch (nextFirst+31))*p.heads
      by_cases hh : g/l.block < cutoff
      · have hSelected : Nonempty (SchedulerWarpReached l X g 2750
            (fun i => activeDrainSelectedFrame p l (warpLane l g i) nextFirst)
            (shuffles+7) votes ends) := by
          apply scan.advanceLocal
          intro i hi
          have hLane := (Step.sameWarp_lane hBlock hg hi).1
          obtain ⟨u,hu,hU⟩ := laterRouteLocal hp hLane.1.2.1 hn.le (scan.checkpoint i hi)
          rw [← hLane.1.2.2,ite_eq_left hh] at hU
          exact ⟨u,hu,hU⟩
        obtain ⟨c⟩ := hSelected
        have hLe : first+31 ≤ p.batch := hn.le
        rw [Nat.min_eq_right hLe] at hlo
        exact activeDrainRelinquishOfSelected hp hMax hg hw hn hlo hh c
      · have hAgain : Nonempty (SchedulerWarpReached l X g 2696
            (fun i => activeDrainLoopFrame p l (warpLane l g i) nextFirst)
            (shuffles+7) votes ends) := by
          apply scan.advanceLocal
          intro i hi
          have hLane := (Step.sameWarp_lane hBlock hg hi).1
          obtain ⟨u,hu,hU⟩ := laterRouteLocal hp hLane.1.2.1 hn.le (scan.checkpoint i hi)
          rw [← hLane.1.2.2,ite_eq_right hh] at hU
          exact ⟨u,hu,hU⟩
        obtain ⟨c⟩ := hAgain
        apply ih (p.batch-nextFirst) (by dsimp only [nextFirst] at *; omega)
          nextFirst (shuffles+7) rfl hn.le (Nat.le_of_not_gt hh) c

/-- Every recorded active MMA drain reaches its actual relinquish collective after
the bounded scan of arbitrary request groups. -/
theorem ActiveDrainNeighbors.relinquishOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (c : ActiveDrainNeighbors p l X g) :
    MmaRelinquishPrefix l X g := by
  have h := c.firstRoute hp hMax hg
  by_cases hFirst : g/l.block < tilePrefix p (min p.batch 31)*p.heads
  · rw [ite_eq_left hFirst] at h
    obtain ⟨s⟩ := h
    have hz : tilePrefix p 0 = 0 := by simp [tilePrefix]
    have hb : 0 < p.batch := by
      by_contra! hn
      have hZero : min p.batch 31 = 0 := by omega
      rw [hZero,hz,Nat.zero_mul] at hFirst
      exact Nat.not_lt_zero _ hFirst
    exact activeDrainRelinquishOfSelected hp hMax hg hw hb
      (by rw [hz,Nat.zero_mul]; exact Nat.zero_le _) hFirst s
  · rw [ite_eq_right hFirst] at h
    obtain ⟨s⟩ := h
    exact relinquishOfLoop hp hMax hCuQ hg hw p.batch 0 (c.shuffles+6) (Nat.sub_zero _)
      (Nat.zero_le _) (Nat.le_of_not_gt hFirst) s

end PTX.Kernels.TmlFa4Fwd.Mma

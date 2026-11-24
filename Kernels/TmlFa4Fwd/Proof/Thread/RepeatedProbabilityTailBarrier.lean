-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
public import Lemmas.Order.WarpBarOrdinal
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
import Lemmas.Step.WarpBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread.Scores

private theorem tailBarrierOut {l : Launch} {g : Nat} (r : Round) {t : TState}
    {F : List (Nat × Value)} (ht : At t (probabilityWaitPc r true+1) F) :
    out kernel Assumptions.all l g t = .ev (.warpBar (2^32-1) (next t)) := by
  have hSite : t.pc = barHead r := ht.1
  rw [out_event ht.2.2.2.1 (hSite.symm ▸ barCode r) rfl rfl]
  change Out.ev (warpBarTmpl l g t (.imm (-1))) = _
  have hMask : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2^32-1 := by decide
  simp only [warpBarTmpl,readBits,pure,Except.pure,hMask,allLanesInTailMask,↓reduceIte]

private theorem tailBarrierAtRecordedPos {l : Launch} {X : Execution} {g : Nat}
    (r : Round) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (probabilityWaitPc r true+1) F)
    (hMore : c.pos < (X.tr g).length) :
    ∃ label, X.WarpBar (g,c.pos) (2^32-1) label ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some (next c.ready)) ∧
      Run kernel Assumptions.all l g (next c.ready) ((X.tr g).drop (c.pos+1)) c.ending := by
  have hOut := tailBarrierOut (l := l) (g := g) r c.checkpoint
  have hNext := Next.mk c.localSteps hOut
  obtain ⟨_,_,he,⟨label,rfl,hAfter⟩,hTail⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_,_,h⟩; cases h) c.remaining
    (fun hNil => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hAfter
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some (next c.ready)) :=
    by
      rw [List.take_add_one,show (X.tr g)[c.pos]? = _ from he]
      exact c.recorded.snoc c.localSteps ⟨_,hOut,label,rfl,rfl⟩
  exact ⟨label,⟨_,he⟩,hPast,hTail⟩

/-- Aligned full-warp P tail cursors reach the actual rendezvous for the same
visit. The ordinal distinguishes this visit from earlier occurrences of its PC. -/
theorem warpTailProbabilityBarrierOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {lead : Nat} (r : Round) (ordinal : Nat) {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (probabilityWaitPc r true+1) (F g))
    (hRank : ∀ g (hw : SameWarp l lead g), warpBars X g (input g hw).pos = ordinal) :
    ∀ g (hw : SameWarp l lead g),
      let c := input g hw
      ∃ label, ∃ u : OpeningTripCursor l X g (probabilityWaitPc r true+1+1) (F g),
        X.WarpBar (g,c.pos) (2^32-1) label ∧ u.pos = c.pos+1 ∧
        u.ready.regs = c.ready.regs ∧ u.ending = c.ending ∧ warpBars X g u.pos = ordinal+1 := by
  intro g hw
  let c := input g hw
  have hrs : warpBars X g c.pos = ordinal := hRank g hw
  have hPresent : c.pos < (X.tr g).length := by
    by_contra! hShort
    have hLast := Nat.le_antisymm c.bounded hShort
    have hEnds (peer : Nat) (hPeer : SameWarp l g peer) :
        (input peer (Step.sameWarp_trans hw hPeer)).pos = (X.tr peer).length := by
      let h := Step.sameWarp_trans hw hPeer
      let d := input peer h
      apply Nat.le_antisymm d.bounded
      by_contra! hOther
      obtain ⟨label,hArrived,_,_⟩ := tailBarrierAtRecordedPos r d hOther
      obtain ⟨j,hPartner⟩ := WarpBar.partner hMax.1 (sameWarp_symm hPeer) hArrived
        (allLanesInTailMask l g)
      have hMember {a b : Nat} (i mask inst : Nat) (h : X.WarpBar (a,i) mask inst) :
          electMember mask (laneOf l b) :=
        (actualFullWarpBarrier hMax.1 h).symm ▸ allLanesInTailMask l b
      have hSameRank := WarpBar.ordinal_eq hMax.1 (sameWarp_symm hPeer)
        (hMember (a := peer) (b := g)) (hMember (a := g) (b := peer)) hPartner
      obtain ⟨_,_,_,hOwn⟩ := hPartner
      have hj : j+1 ≤ c.pos := (WarpBar.lt_len hOwn).trans_le hShort
      have hCount := countP_take_mono Execution.isWarpBar (X.tr g) hj
      change warpBars X g (j+1) ≤ warpBars X g c.pos at hCount
      rw [WarpBar.warpBars_succ hOwn,← hSameRank,hrs] at hCount
      have hOtherRank : warpBars X peer d.pos = ordinal := hRank peer h
      omega
    apply hMax.not_grows
    refine Step.warpBar_counted_extension hMax.1 (fun _ => probabilityWaitPc r true+1)
      hw.1.2.1 (fun lane hMem => ⟨_,Step.sameWarp_lane (by rw [hp.block]) hw.1.2.1 hMem.1⟩)
      (fun peer _ => allLanesInTailMask l peer) ?_ ?_ ?_ ?_
    · intro peer hPeer
      let d := input peer (Step.sameWarp_trans hw hPeer)
      exact .inl (List.ne_nil_of_length_pos ((hEnds peer hPeer) ▸ d.positive))
    · intro peer hPeer
      exact (input peer (Step.sameWarp_trans hw hPeer)).released (hEnds peer hPeer)
    · intro peer hPeer label
      let d := input peer (Step.sameWarp_trans hw hPeer)
      have hrun : Run kernel Assumptions.all l peer {} (X.tr peer) (some d.before) := by
        have hEnd : d.pos = (X.tr peer).length := hEnds peer hPeer
        simpa only [hEnd,List.take_length] using d.recorded
      exact ⟨d.before,d.ready,some (next d.ready),hrun,d.localSteps,
        ⟨_,tailBarrierOut r d.checkpoint,label,by rw [d.checkpoint.1],rfl⟩⟩
    · intro label
      exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes fun _ => by rfl)
  obtain ⟨label,he,hPast,hTail⟩ := tailBarrierAtRecordedPos r c hPresent
  have hRelease (hLast : c.pos+1 = (X.tr g).length) : Step.Released l X g := by
    constructor
    intro site actual hGet _
    have hIdx : (X.tr g).length-1 = c.pos := by omega
    rw [hIdx]
    exact WarpBar.ready hMax.1 he
  let t := next c.ready
  let u : OpeningTripCursor l X g (probabilityWaitPc r true+1+1) (F g) :=
    ⟨c.pos+1,t,t,c.ending,Nat.succ_pos _,(WarpBar.lt_len he),hRelease,
      c.checkpoint.next,hPast,hTail,.refl⟩
  exact ⟨label,u,he,rfl,rfl,rfl,(WarpBar.warpBars_succ he).trans (congrArg (·+1) hrs)⟩

end PTX.Kernels.TmlFa4Fwd.Softmax

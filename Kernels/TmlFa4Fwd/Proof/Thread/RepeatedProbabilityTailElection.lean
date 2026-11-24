-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityTailBarrier
public import Lemmas.Order.ElectOrdinal
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Lemmas.Step.WarpElect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread.Scores

private def electedTailState (l : Launch) (g : Nat) (r : Round) (t : TState) (leader : Nat) :
    TState :=
  next (setReg (setReg t (tailElectLane r) (b32 leader)) (tailElectPred r)
    (.pred (laneOf l g == leader)))

private theorem tailElectionOut {l : Launch} {g : Nat} (r : Round) {t : TState}
    {F : List (Nat × Value)} (ht : At t (probabilityWaitPc r true+2) F) :
    out kernel Assumptions.all l g t = .ev (.elect (2^32-1) (electedTailState l g r t)) := by
  have hSite : t.pc = electHead r := by
    change t.pc = probabilityWaitPc r true+1+1
    rw [ht.1,Nat.add_assoc]
  rw [out_event ht.2.2.2.1 (hSite.symm ▸ electCode r) rfl rfl]
  change Out.ev (electTmpl l g t (some (tailElectLane r)) (tailElectPred r) (.imm (-1))) = _
  have hMask : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2^32-1 := by decide
  simp only [electTmpl,readBits,pure,Except.pure,hMask,allLanesInTailMask,↓reduceIte]
  rfl

private theorem tailElectionAtRecordedPos {l : Launch} {X : Execution} {g : Nat}
    (r : Round) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (probabilityWaitPc r true+2) F)
    (hMore : c.pos < (X.tr g).length) :
    ∃ label leader, X.Elect (g,c.pos) (probabilityWaitPc r true+2) (2^32-1) label leader ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1))
        (some (electedTailState l g r c.ready leader)) ∧
      Run kernel Assumptions.all l g (electedTailState l g r c.ready leader)
        ((X.tr g).drop (c.pos+1)) c.ending := by
  have hOut := tailElectionOut (l := l) (g := g) r c.checkpoint
  have hNext := Next.mk c.localSteps hOut
  obtain ⟨_,_,he,⟨label,leader,rfl,hAfter⟩,hTail⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_,_,_,h⟩; cases h) c.remaining
    (fun hNil => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hAfter
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1))
      (some (electedTailState l g r c.ready leader)) := by
    rw [List.take_add_one,show (X.tr g)[c.pos]? = _ from he]
    exact c.recorded.snoc c.localSteps ⟨_,hOut,label,leader,rfl,rfl⟩
  rw [c.checkpoint.1] at he
  exact ⟨label,leader,he,hPast,hTail⟩

/-- The aligned actual post-rendezvous warp elects its tail publisher. All earlier
elections use a full mask, so a returned peer occurrence cannot match an earlier one. -/
theorem warpTailProbabilityElectionOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {lead : Nat} (r : Round) (ordinal : Nat) {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (probabilityWaitPc r true+2) (F g))
    (hRank : ∀ g (hw : SameWarp l lead g), elections X g (input g hw).pos = ordinal)
    (hLaneFresh : ∀ g, ∀ pair ∈ F g, pair.1 ≠ tailElectLane r)
    (hPredFresh : ∀ g, ∀ pair ∈ F g, pair.1 ≠ tailElectPred r) :
    ∀ g (hw : SameWarp l lead g),
      let c := input g hw
      ∃ label, ∃ leader : Fin 32,
        ∃ u : OpeningTripCursor l X g (probabilityWaitPc r true+3)
          ((tailElectPred r,.pred (laneOf l g == leader.val))::
            (tailElectLane r,b32 leader.val)::F g),
          X.Elect (g,c.pos) (probabilityWaitPc r true+2) (2^32-1) label leader ∧
          u.pos = c.pos+1 ∧ u.ending = c.ending ∧ elections X g u.pos = ordinal+1 := by
  intro g hw
  let c := input g hw
  have hrs : elections X g c.pos = ordinal := hRank g hw
  have hPresent : c.pos < (X.tr g).length := by
    by_contra! hShort
    have hEnds (peer : Nat) (hPeer : SameWarp l g peer) :
        (input peer (Step.sameWarp_trans hw hPeer)).pos = (X.tr peer).length := by
      let h := Step.sameWarp_trans hw hPeer
      let d := input peer h
      apply Nat.le_antisymm d.bounded
      by_contra! hMore
      obtain ⟨label,leader,he,_,_⟩ := tailElectionAtRecordedPos r d hMore
      obtain ⟨j,_,pc,mask,mask',label',w,z,hE,hF⟩ :=
        ElectOrd.partner hMax.1 (sameWarp_symm hPeer) he (allLanesInTailMask l g)
      have hOrd := electOrdinal hMax.1
        (ElectMutual.of_full (Thread.actualFullElectionMask hMax.1)) (sameWarp_symm hPeer) hE hF
      have hj : j+1 ≤ c.pos := (len_of_get hF).trans_le hShort
      have hCount := countP_take_mono isElectEv (X.tr g) hj
      change elections X g (j+1) ≤ elections X g c.pos at hCount
      rw [ElectOrd.elections_succ hF,hrs] at hCount
      have hOtherRank : elections X peer d.pos = ordinal := hRank peer h
      change elections X peer d.pos = elections X g j at hOrd
      omega
    obtain ⟨leader,hLeader,hDet⟩ :=
      Step.exists_leader hMax.1 (g := g) (allLanesInTailMask l g)
    apply hMax.not_grows
    refine Step.elect_counted_extension (pc := probabilityWaitPc r true+2) hMax.1 hw.1.2.1
      (fun lane hm => ⟨_,Step.sameWarp_lane (by rw [hp.block]) hw.1.2.1 hm.1⟩)
      (fun peer _ => allLanesInTailMask l peer) hLeader hDet ?_ ?_ ?_ ?_
    · intro peer hPeer
      let d := input peer (Step.sameWarp_trans hw hPeer)
      exact .inl (List.ne_nil_of_length_pos ((hEnds peer hPeer) ▸ d.positive))
    · intro peer hPeer
      exact (input peer (Step.sameWarp_trans hw hPeer)).released (hEnds peer hPeer)
    · intro peer hPeer label
      let d := input peer (Step.sameWarp_trans hw hPeer)
      have hRun : Run kernel Assumptions.all l peer {} (X.tr peer) (some d.before) := by
        have hEnd : d.pos = (X.tr peer).length := hEnds peer hPeer
        simpa only [hEnd,List.take_length] using d.recorded
      exact ⟨d.before,d.ready,some (electedTailState l peer r d.ready leader),
        hRun,d.localSteps,⟨_,tailElectionOut r d.checkpoint,label,leader,by
          rw [d.checkpoint.1],rfl⟩⟩
    · intro label
      exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes fun _ => by rfl)
  obtain ⟨label,leader,he,hPast,hTail⟩ := tailElectionAtRecordedPos r c hPresent
  have hLead := (hMax.1.elect.1 _ _ _ _ _ he).2.2.1
  let u := electedTailState l g r c.ready leader
  let facts := (tailElectPred r,.pred (laneOf l g == leader))::
    (tailElectLane r,b32 leader)::F g
  have hReady : At u (probabilityWaitPc r true+3) facts := by
    have hd : tailElectLane r ≠ tailElectPred r := by cases r <;> decide
    have hu : At (next (setReg c.ready (tailElectLane r) (b32 leader)))
        ((probabilityWaitPc r true+2)+1) ((tailElectLane r,b32 leader)::F g) :=
      c.checkpoint.set (hLaneFresh g)
    have hFresh (pair : Nat × Value) (hp : pair ∈ (tailElectLane r,b32 leader)::F g) :
        pair.1 ≠ tailElectPred r := by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hd
      · exact hPredFresh g pair hp
    exact ⟨congrArg (·+1) c.checkpoint.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,
      Function.update_self ..,holds_update hu.2.2.2.2 hFresh⟩
  have hRelease (hLast : c.pos+1 = (X.tr g).length) : Step.Released l X g := by
    constructor
    intro site actual _ _
    have hIndex : (X.tr g).length-1 = c.pos := by omega
    rw [hIndex]
    exact elect_ready hMax.1 he
  let after : OpeningTripCursor l X g (probabilityWaitPc r true+3) facts :=
    ⟨c.pos+1,u,u,c.ending,Nat.succ_pos _,len_of_get he,hRelease,hReady,hPast,hTail,.refl⟩
  exact ⟨label,⟨leader,hLead⟩,after,he,rfl,rfl,(ElectOrd.elections_succ he).trans
    (congrArg (·+1) hrs)⟩

end PTX.Kernels.TmlFa4Fwd.Softmax

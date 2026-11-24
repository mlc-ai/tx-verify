-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWarpBar
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.WarpElect
import Lemmas.Order.ElectOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

/-- Register state returned by the first full-warp probability election. -/
def tailElectionReturn (l : Launch) (g : Nat) (t : TState) (leader : Nat) : TState :=
  next (setReg (setReg t 3944 (b32 leader)) 623 (.pred (laneOf l g == leader)))

private theorem tailElectOut {l : Launch} {g : Nat} {t : TState} (ht : At t 4859 []) :
    out kernel Assumptions.all l g t = .ev (.elect 4294967295 (tailElectionReturn l g t)) := by
  rw [out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_4859) rfl rfl]
  change Out.ev (electTmpl l g t (some 3944) 623 (.imm (-1))) = _
  have hBits : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 4294967295 := by decide
  simp only [electTmpl,readBits,pure,Except.pure,hBits,PTX.electMember_full,↓reduceIte]
  rfl

set_option maxRecDepth 100000 in
private theorem electionNoBack :
    (kernel.code.drop 4859).all (fun i => Thread.staysPastEvent 4859 i.op) = true := by kernel_rfl

private theorem electionSegmentFloor : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (4859 ≤ seg.stop)
    | none => false) = true := by kernel_rfl

/-- A lane at the opening P tail election records the leader event before the tail release. -/
structure OpeningProbabilityElection (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  barrier : OpeningProbabilityWarpBar p l X g stage
  leader : Fin 32
  label : Nat
  elected : X.Elect (g,barrier.wait.tail.main.main.stored.wait.statistics.index+10)
    4859 4294967295 label leader
  recorded : Run kernel Assumptions.all l g {}
    ((X.tr g).take (barrier.wait.tail.main.main.stored.wait.statistics.index+11))
    (some (tailElectionReturn l g (next (next barrier.wait.tail.state)) leader))
  continuation : Run kernel Assumptions.all l g
    (tailElectionReturn l g (next (next barrier.wait.tail.state)) leader)
    ((X.tr g).drop (barrier.wait.tail.main.main.stored.wait.statistics.index+11))
    barrier.wait.tail.main.main.stored.wait.statistics.ending

/-- An earlier-role event in this lane precedes its actual opening P-tail election. -/
theorem OpeningProbabilityElection.afterEarlierEvent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g k : Nat} {stage : Fin 2} (c : OpeningProbabilityElection p l X g stage)
    {e : Event} (he : X.get (g,k) = some e) (hBefore : e.pc < 4859) :
    k < c.barrier.wait.tail.main.main.stored.wait.statistics.index+10 :=
  Thread.traceOrderOfPcFloor hX electionNoBack electionSegmentFloor he c.elected
    hBefore (Nat.le_refl _)

private theorem tailElectionRecorded {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {stage : Fin 2} (c : OpeningProbabilityWarpBar p l X g stage)
    (hMore : c.wait.tail.main.main.stored.wait.statistics.index+10 < (X.tr g).length) :
    Nonempty (OpeningProbabilityElection p l X g stage) := by
  let t := next (next c.wait.tail.state)
  let pos := c.wait.tail.main.main.stored.wait.statistics.index+10
  have ht : At t 4859 [] := c.wait.tail.ready.next.next
  have hOut := tailElectOut (l := l) (g := g) ht
  have hn := Next.mk (Relation.ReflTransGen.refl (a := t)) hOut
  obtain ⟨_,_,he,⟨label,leader,rfl,hAfter⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,_,_,h⟩; cases h) c.continuation
    (fun hNil => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hAfter
  have hGet : X.Elect (g,pos) 4859 4294967295 label leader := by
    change X.get (g,pos) = _
    rwa [ht.1] at he
  have hLeader := (hX.elect.1 _ _ _ _ _ hGet).2.2.1
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1))
      (some (tailElectionReturn l g t leader)) := by
    rw [List.take_add_one,show (X.tr g)[pos]? = _ from he]
    exact c.recorded.snoc .refl ⟨_,hOut,label,leader,rfl,rfl⟩
  exact ⟨⟨c,⟨leader,hLeader⟩,label,hGet,hPast,hTail⟩⟩

/-- A whole active warp past its first P-tail rendezvous reaches its actual election. -/
theorem OpeningProbabilityWarpBar.electionOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (c : OpeningProbabilityWarpBar p l X g stage)
    (hPeers : ∀ peer, SameWarp l g peer → Nonempty (OpeningProbabilityWarpBar p l X peer stage)) :
    Nonempty (OpeningProbabilityElection p l X g stage) := by
  classical
  let pos := c.wait.tail.main.main.stored.wait.statistics.index+10
  obtain ⟨pc,hBarrier⟩ := c.arrived
  have hOwn : pos ≤ (X.tr g).length := len_of_get hBarrier
  by_cases hMore : pos < (X.tr g).length
  · exact tailElectionRecorded hMax.1 c hMore
  have hLast : pos = (X.tr g).length := Nat.le_antisymm hOwn (Nat.le_of_not_lt hMore)
  let states (peer : Nat) (h : SameWarp l g peer) := Classical.choice (hPeers peer h)
  have hEnds (peer : Nat) (h : SameWarp l g peer) :
      (states peer h).wait.tail.main.main.stored.wait.statistics.index+10 = (X.tr peer).length := by
    let o := states peer h
    obtain ⟨pc',hOther⟩ := o.arrived
    have hBound := len_of_get hOther
    apply Nat.le_antisymm hBound
    by_contra! hLater
    obtain ⟨a⟩ := tailElectionRecorded hMax.1 o hLater
    obtain ⟨j,p1,p2,m1,m2,label,l1,l2,hFrom,hMatch⟩ :=
      ElectOrd.partner hMax.1 (sameWarp_symm h) a.elected (PTX.electMember_full l g)
    have hSame := (hMax.1.elect.2.1 _ _ _ _ _ _ _ _ _ hFrom hMatch (sameWarp_symm h)).1
    have hP1 := congrArg Event.pc (Option.some.inj (a.elected.symm.trans hFrom))
    change 4859 = p1 at hP1
    have hP2 : 4859 = p2 := hP1.trans hSame
    rw [← hP2] at hMatch
    change X.get (g,j) = some ⟨4859,.elect m2 label l2⟩ at hMatch
    have hLate := Thread.traceOrderOfPcFloor hMax.1 electionNoBack electionSegmentFloor
      c.wait.waited hMatch (show probabilityWaitPc .first true < 4859 by decide) (Nat.le_refl _)
    have hj := len_of_get hMatch
    have hNe : j ≠ c.wait.tail.main.main.stored.wait.statistics.index+9 := by
      intro eq
      rw [eq,hBarrier] at hMatch
      cases hMatch
    change j+1 ≤ (X.tr g).length at hj
    dsimp [pos] at hLast
    omega
  obtain ⟨leader,hLeader,hDet⟩ := Step.exists_leader hMax.1 (g := g) (PTX.electMember_full l g)
  exfalso
  apply hMax.not_grows
  refine Step.elect_counted_extension (pc := 4859) hMax.1 hg
    (fun lane hm => ⟨_,Step.sameWarp_lane (by rw [hp.block]) hg hm.1⟩)
    (fun _ _ => PTX.electMember_full ..) hLeader hDet ?_ ?_ ?_ ?_
  · intro peer hPeer
    apply Or.inl
    apply List.ne_nil_of_length_pos
    rw [← hEnds peer hPeer]
    omega
  · intro peer hPeer
    let o := states peer hPeer
    have hEnd := hEnds peer hPeer
    refine ⟨fun pc kind hGet _ => ?_⟩
    have hIndex : (X.tr peer).length-1 = o.wait.tail.main.main.stored.wait.statistics.index+9 := by
      change o.wait.tail.main.main.stored.wait.statistics.index+10 = _ at hEnd
      omega
    rw [hIndex]
    exact WarpBar.ready hMax.1 o.arrived
  · intro peer hPeer label
    let o := states peer hPeer
    let t := next (next o.wait.tail.state)
    have ht : At t 4859 [] := o.wait.tail.ready.next.next
    have hEnd : o.wait.tail.main.main.stored.wait.statistics.index+10 = (X.tr peer).length :=
      hEnds peer hPeer
    have hRun : Run kernel Assumptions.all l peer {} (X.tr peer) (some t) := by
      simpa only [hEnd,List.take_length] using o.recorded
    exact ⟨t,t,some (tailElectionReturn l peer t leader),hRun,.refl,
      ⟨_,tailElectOut ht,label,leader,by rw [ht.1],rfl⟩⟩
  · intro label
    exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl (noNewRead_appendLanes fun _ => by rfl)

end PTX.Kernels.TmlFa4Fwd.Softmax

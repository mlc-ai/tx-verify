-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityTail
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
import Lemmas.Order.WarpBarOrdinal
import Lemmas.Step.WarpBar
import Lemmas.Step.DrainInOrder
import Lemmas.Flow.NotWarpBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

private def notTailWarpBarrier (op : Op) : Bool :=
  match op with
  | .warp w => w.kind != .barWarp
  | _ => true

set_option maxRecDepth 100000 in
private theorem firstWarpBarrierSite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {site mask inst : Nat}
    (he : X.get i = some ⟨site,.warpBar mask inst⟩) : 4858 ≤ site := by
  by_contra! hEarly
  have hCode : (kernel.code.take 4858).all (fun i => notTailWarpBarrier i.op) = true := by
    kernel_rfl
  rcases get_source hX he with ⟨_,hBad⟩ | ⟨_,ins,_,_,hGet,hFires⟩
  · cases hBad
  have hTake : (kernel.code.take 4858)[site]? = some ins := by
    rwa [List.getElem?_take_of_lt hEarly]
  have hChecked := List.all_eq_true.mp hCode _ (List.mem_of_getElem? hTake)
  apply fires_notWarpBar_op (op := ins.op) _ hFires mask inst rfl
  intro w hOp hKind
  simp [notTailWarpBarrier,hOp,hKind] at hChecked

set_option maxRecDepth 100000 in
private theorem tailNoBack :
    (kernel.code.drop 4858).all (fun i => Thread.staysPastEvent 4858 i.op) = true := by kernel_rfl

private theorem tailSegmentFloor : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (4858 ≤ seg.stop)
    | none => false) = true := by kernel_rfl

private theorem tailWarpBarrierOut {l : Launch} {g : Nat} {t : TState} (ht : At t 4858 []) :
    out kernel Assumptions.all l g t = .ev (.warpBar 4294967295 (next t)) := by
  rw [out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_4858) rfl rfl]
  change Out.ev (warpBarTmpl l g t (.imm (-1))) = _
  have hBits : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 4294967295 := by decide
  simp only [warpBarTmpl,readBits,pure,Except.pure,hBits,PTX.electMember_full,↓reduceIte]

/-- The actual first tail warp rendezvous carries the lane trace to its next election. -/
structure OpeningProbabilityWarpBar (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  wait : OpeningProbabilityTailWait p l X g stage
  label : Nat
  arrived : X.WarpBar (g,wait.tail.main.main.stored.wait.statistics.index+9) 4294967295 label
  recorded : Run kernel Assumptions.all l g {}
    ((X.tr g).take (wait.tail.main.main.stored.wait.statistics.index+10))
    (some (next (next wait.tail.state)))
  continuation : Run kernel Assumptions.all l g (next (next wait.tail.state))
    ((X.tr g).drop (wait.tail.main.main.stored.wait.statistics.index+10))
    wait.tail.main.main.stored.wait.statistics.ending

private theorem tailWarpBarrierRecorded {p : Params} {l : Launch} {X : Execution}
    {g : Nat} {stage : Fin 2} (c : OpeningProbabilityTailWait p l X g stage)
    (hMore : c.tail.main.main.stored.wait.statistics.index+9 < (X.tr g).length) :
    Nonempty (OpeningProbabilityWarpBar p l X g stage) := by
  let t := next c.tail.state
  let pos := c.tail.main.main.stored.wait.statistics.index+9
  have ht : At t 4858 [] := c.tail.ready.next
  have hOut := tailWarpBarrierOut (l := l) (g := g) ht
  have hNext : Next kernel Assumptions.all l g t t (.warpBar 4294967295 (next t)) := ⟨.refl,hOut⟩
  obtain ⟨_,_,he,⟨label,rfl,hAfter⟩,hTail⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_,_,h⟩; cases h) c.continuation
    (fun hNil => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hAfter
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next t)) := by
    rw [List.take_add_one,show (X.tr g)[pos]? = _ from he]
    exact c.recorded.snoc .refl ⟨_,hOut,label,rfl,rfl⟩
  exact ⟨⟨c,label,⟨_,he⟩,hPast,hTail⟩⟩

/-- The warp's actual fourth stores and tail waits force its first probability rendezvous. -/
theorem OpeningProbabilityTailWait.warpBarOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (c : OpeningProbabilityTailWait p l X g stage)
    (hPeers : ∀ peer, SameWarp l g peer → Nonempty (OpeningProbabilityTailWait p l X peer stage)) :
    Nonempty (OpeningProbabilityWarpBar p l X g stage) := by
  classical
  let pos := c.tail.main.main.stored.wait.statistics.index+9
  have hOwn : pos ≤ (X.tr g).length := len_of_get c.waited
  by_cases hMore : pos < (X.tr g).length
  · exact tailWarpBarrierRecorded c hMore
  have hLast : pos = (X.tr g).length := Nat.le_antisymm hOwn (Nat.le_of_not_lt hMore)
  let states (peer : Nat) (h : SameWarp l g peer) := Classical.choice (hPeers peer h)
  have hEnds (peer : Nat) (h : SameWarp l g peer) :
      (states peer h).tail.main.main.stored.wait.statistics.index+9 = (X.tr peer).length := by
    let o := states peer h
    have hBound := len_of_get o.waited
    apply Nat.le_antisymm hBound
    by_contra! hLater
    obtain ⟨a⟩ := tailWarpBarrierRecorded o hLater
    obtain ⟨j,mask,label,_,hA⟩ := WarpBar.partner hMax.1 (sameWarp_symm h) a.arrived
      (PTX.electMember_full l g)
    obtain ⟨site,hSite⟩ := hA
    have hLate := Thread.traceOrderOfPcFloor hMax.1 tailNoBack tailSegmentFloor c.waited hSite
      (show probabilityWaitPc .first true < 4858 by decide) (firstWarpBarrierSite hMax.1 hSite)
    have hj := len_of_get hSite
    dsimp [pos] at hLast
    change j+1 ≤ (X.tr g).length at hj
    omega
  exfalso
  apply hMax.not_grows
  refine Step.warpBar_counted_extension hMax.1 (fun _ => 4858) hg
    (fun lane hMem => ⟨_,Step.sameWarp_lane (by rw [hp.block]) hg hMem.1⟩)
    (fun _ _ => PTX.electMember_full ..) ?_ ?_ ?_ ?_
  · intro peer hPeer
    apply Or.inl
    apply List.ne_nil_of_length_pos
    rw [← hEnds peer hPeer]
    omega
  · intro peer hPeer
    let o := states peer hPeer
    have hLocal (q : Nat) (hq : q ∈ warpLanes l peer) : ∃ i, X.TcK (q,i) 10 := by
      obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hq
      have hl : lane < 32 := (List.mem_range.mp hLane).trans_le (Nat.min_le_left ..)
      have hSame := (Step.sameWarp_lane (by rw [hp.block]) hPeer.1.2.1 hl).1
      have h := Step.sameWarp_trans hPeer hSame
      exact ⟨_,(states _ h).ordinal⟩
    exact probabilityCollectiveReleased o.waited (.inr (.inl rfl)) o.ordinal.2 hLocal
      (hEnds peer hPeer)
  · intro peer hPeer label
    let o := states peer hPeer
    let t := next o.tail.state
    have ht : At t 4858 [] := o.tail.ready.next
    have hEnd : o.tail.main.main.stored.wait.statistics.index+9 = (X.tr peer).length :=
      hEnds peer hPeer
    have hRun : Run kernel Assumptions.all l peer {} (X.tr peer) (some t) := by
      simpa only [hEnd,List.take_length] using o.recorded
    exact ⟨t,t,some (next t),hRun,.refl,⟨_,tailWarpBarrierOut ht,label,by rw [ht.1],rfl⟩⟩
  · intro label
    exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl (noNewRead_appendLanes fun _ => by rfl)

end PTX.Kernels.TmlFa4Fwd.Softmax

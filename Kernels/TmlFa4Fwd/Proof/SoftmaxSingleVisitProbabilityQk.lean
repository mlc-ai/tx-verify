-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitScoreWrites
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma Epilogue

/-- The packed probability columns reuse the upper half of a score stage. -/
theorem probabilityCellAsScore (l : Launch) (g : Nat) (stage : Fin 2) (q : Fin 4)
    {word : Nat} (hWord : word < 16) :
    let scoreQuarter : Fin 4 := ⟨2+q.val/2,by have := q.isLt; omega⟩
    let scoreWord : Fin 32 := ⟨16*(q.val%2)+word,by
      have := Nat.mod_lt q.val (by decide : 0<2)
      omega⟩
    tcDataCell l g .s32x32b (probabilityAddress l g stage q) word =
      tcDataCell l g .s32x32b (scoreAddress l g stage scoreQuarter) scoreWord.val := by
  dsimp only
  have hBase := scoreColumn_range stage
  have hQ := q.isLt
  rw [probabilityAddress,scoreAddress,tcDataCell_warp32 _ _ _ (by unfold probabilityColumn; omega),
    tcDataCell_warp32 _ _ _ (by change scoreColumn stage+32*(2+q.val/2) < 512; omega)]
  congr 1
  change probabilityColumn stage + 16*q.val + word =
    scoreColumn stage + 32*(2+q.val/2) + (16*(q.val%2)+word)
  unfold probabilityColumn
  omega

set_option maxRecDepth 100000 in
private theorem afterScoreWaitCode :
    (kernel.code.drop 3428).all (fun i => Thread.staysPastEvent 3428 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterScoreWaitSegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match PTX.Assumption.cuteExp2.matchAt kernel pc with
      | some seg => decide (3428 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

/-- The only MMA writes to a single-visit probability cell are initial QK fragments,
and the consumer's first score acquire orders them before that cell's P store. -/
theorem singleVisitMmaWriteBeforeProbabilityStore {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hComplete : Complete l X) (hFootprint : OutputFootprint p X)
    {batch : Nat} {stage : Fin 2} {producer consumer commit wait : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ producer/l.block)
    (hHi : producer/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (producer/l.block)).1 = 1)
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    {output : EvId} {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer/l.block = output.1/l.block)
    (q : Fin 4) {word : Nat} (hWord : word < 16) {store : Nat} {vals : List Value}
    (he : X.get (consumer,store) = some ⟨probabilityPc .first q,
      .tc (.st (probabilityAddress l consumer stage q) vals .s32x32b)⟩)
    {other : EvId} (hWrite : X.MmaCell other (tcDataCell l consumer .s32x32b
      (probabilityAddress l consumer stage q) word)) :
    WriteBefore l X other (consumer,store) := by
  obtain ⟨start,hIssues⟩ := firstObservedQkIssues hp hX hPhase hOutput hOutputCta
  rw [probabilityCellAsScore l consumer stage q hWord] at hWrite
  obtain ⟨frag,rfl⟩ := singleVisitScoreMmaWriter hp hX hComplete hFootprint hb hLo hHi hTrip
    hPhase hOutput hOutputCta hIssues _ _ hWrite
  have hEarlier := firstObservedQkBeforeCommit hX hPhase frag (hIssues frag)
  have hSite : 3428 ≤ probabilityPc .first q := by fin_cases q <;> decide
  have hOrder : wait < store :=
    Thread.traceOrderOfPcFloor hX afterScoreWaitCode afterScoreWaitSegments
      hPhase.waitEvent he (show 3425 < 3428 by decide) hSite
  have hAfter : po X (consumer,wait) (consumer,store) :=
    po_of_not_access rfl hOrder (PTX.len_of_get he) (by rw [he]; rfl)
  have hIssue : X.TcAsync (producer,start+frag.val) := .inl
    ⟨scoreColumn (Mma.qkStage (firstQkBlock stage)),
      Mma.qkOperands l producer (firstQkBlock stage) frag 0,decide (frag.val ≠ 0),
      List.replicate 4 0,_,hIssues frag⟩
  exact .inl (.inl (.inl ⟨(consumer,wait),.cta,
    firstQkPhase_observed hX hPhase hIssue hEarlier,
    PTX.MbarRing.Unit.Gate.scopesMeet hPhase.sameCta .cluster .cta,.single (.inl hAfter)⟩))

end PTX.Kernels.TmlFa4Fwd.Softmax

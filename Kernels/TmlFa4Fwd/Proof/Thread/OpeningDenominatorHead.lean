-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningLoopRegisters
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalNumerics
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Numeric

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hRole : Prologue.warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {last pc : Nat}
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩)
    (hRow : 128*(2*(Epilogue.assignedCoordinates p batch (g/l.block)).1+stage.val)+
      (g%l.block)%128 < p.qLength batch)
include hp hMax hFrame hg stage hRole hb hLo hHi hExit hRow

/-- The loop head is reached by the recorded lane with the first denominator
and actual number of biased and plain visits remaining. -/
theorem openingDenominatorHeadWithRegistersOfMaximalExit :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let blocks := Mma.trips p batch coords.1
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    let mx := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
      (List.range 128)
    let ref := firstReference p batch coords.2 row blocks
    let mass := (2 : ℝ)^(-ref)*maskedBlockSum (p.keyCount batch row) blocks 0
      (weight p batch coords.2 row)
    let split := firstPlainSplit blocks cap
    let biased := firstBiasedRepeats blocks cap
    SoftmaxSumPrefix p batch coords.2 row blocks 1
      (fun _ => mx.map (abiFloat p.scaleLog2Bits * ·)) (fun _ => mass) ∧
    ∃ j u,
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) none ∧
      Thread.Scores.probabilityOrdinal l X (g/l.block) stage 0 (g,j) = 1 ∧
      (if biased = 0 then
        if split = 0 then
          At u 7605 ((1491,b32 split)::firstLoopChoiceFacts blocks split past mx mass)
        else At u 6661 (firstPlainFacts p blocks split past mx mass)
       else At u 5032 (firstBiasedFacts blocks split past mx mass)) ∧
      Holds u.regs (openingDenominatorRegisters p l g) := by
  let coords := Epilogue.assignedCoordinates p batch (g/l.block)
  let tile := coords.1
  let blocks := Mma.trips p batch tile
  let cap := blocks-stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  let split := firstPlainSplit blocks cap
  let biased := firstBiasedRepeats blocks cap
  let row := 128*(2*tile+stage.val)+(g%l.block)%128
  let mx := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
    (List.range 128)
  let ref := firstReference p batch coords.2 row blocks
  let mass := (2 : ℝ)^(-ref)*maskedBlockSum (p.keyCount batch row) blocks 0
    (weight p batch coords.2 row)
  refine ⟨?_,?_⟩
  · have hRef : (mx.map (abiFloat p.scaleLog2Bits * ·)).getD 0 = ref := by
      change (mx.map (abiFloat p.scaleLog2Bits * ·)).getD 0 = abiFloat p.scaleLog2Bits*mx.getD 0
      cases mx <;> simp
    have hInitial := openingSoftmaxSumPrefix p batch coords.2 row blocks
    change SoftmaxSumPrefix p batch coords.2 row blocks 1
      (fun _ => mx.map (abiFloat p.scaleLog2Bits * ·))
      (fun _ => (2 : ℝ)^(-(mx.map (abiFloat p.scaleLog2Bits * ·)).getD 0)*
        maskedBlockSum (p.keyCount batch row) blocks 0 (weight p batch coords.2 row)) at hInitial
    rw [hRef] at hInitial
    exact hInitial
  change ∃ j u, _ ∧ _ ∧ _ ∧ (if biased = 0 then
    if split = 0 then At u 7605 ((1491,b32 split)::firstLoopChoiceFacts blocks split past mx mass)
    else At u 6661 (firstPlainFacts p blocks split past mx mass)
    else At u 5032 (firstBiasedFacts blocks split past mx mass)) ∧
      Holds u.regs (openingDenominatorRegisters p l g)
  have hTile := (Epilogue.assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨hPositive,hCount,hLimit⟩ := Mma.trips_bounds hp hb hTile
  obtain ⟨_,_,hLength⟩ := hp.lengths batch hb
  change 0 < blocks at hPositive
  change blocks ≤ (p.kLength batch+127)/128 at hCount
  have hSigned : blocks+10 < 2^31 := by omega
  have hCap : cap < 2^31 := by dsimp only [cap]; omega
  have hPast : past+256 < 2^31 := by
    change p.kLength batch-p.qLength batch+256*(tile+1) < 2^31 at hLimit
    change (p.kLength batch-p.qLength batch+256*tile)+256 < 2^31
    rw [Nat.mul_succ,← Nat.add_assoc] at hLimit
    exact hLimit
  obtain ⟨j,t,ht,hTrace,hRun,hCount,hRegs⟩ := openingMassWithRegistersOfMaximalExit hp hMax
    hFrame hg
    stage hRole hb hLo hHi hExit hRow
  obtain ⟨u,hLocal,hu⟩ := firstLoopEntryLocal (l := l) (g := g) blocks cap past _ _
    hPositive (by omega) (by dsimp only [cap]; omega) hCap hPast ht
  have reached {v : TState} (h : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v) :
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) v := by
    simpa only [List.append_nil] using hTrace.append (TraceReach.of_local h)
  by_cases hz : biased = 0
  · have hz' : firstBiasedRepeats blocks cap = 0 := hz
    have hu' : At u 6654 (firstLoopChoiceFacts blocks split past mx mass) :=
      by simpa only [hz',ite_true] using hu
    have hSplit : split < blocks := by unfold split firstPlainSplit; omega
    obtain ⟨v,hNext,hv⟩ := firstPlainEntryLocal hp (g := g) blocks split past mx mass
      (by omega) hSplit hu'
    have hPath := hLocal.trans hNext
    refine ⟨j,v,reached hPath,hRun.after_local hPath,hCount,?_,
      openingLoopRegistersLocal (.inl ht.1) hRegs hPath⟩
    simpa only [hz,ite_true] using hv
  · have hz' : firstBiasedRepeats blocks cap ≠ 0 := hz
    refine ⟨j,u,reached hLocal,hRun.after_local hLocal,hCount,?_,
      openingLoopRegistersLocal (.inl ht.1) hRegs hLocal⟩
    simpa only [hz,hz',ite_false] using hu

end PTX.Kernels.TmlFa4Fwd.Softmax

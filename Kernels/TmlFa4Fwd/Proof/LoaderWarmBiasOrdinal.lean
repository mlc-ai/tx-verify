-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasIssueUnique
public import Kernels.TmlFa4Fwd.Proof.LoaderFirstBiasOrigins
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingBiasOrder
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

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue Thread.Loader PTX.Assumption

private theorem earlierBiasSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hBox : BiasSubbox p l X e stage half spec) :
    ∃ pc, X.get e = some ⟨pc,.tensorIssue p.biasMapAddress spec⟩ ∧
      (pc = (inputSite (firstBiasIssueSite stage half)).pc ∨
        pc = warmBiasIssueSite stage half ∨ 1353 ≤ pc) := by
  obtain ⟨i,hs,hh,he⟩ := biasTensorSelectorOfSubbox hp hX hBox
  have classify (i : Fin 10) :
      let s := biasTensorSelector i
      s.issue = (inputSite (firstBiasIssueSite s.stage s.half)).pc ∨
        s.issue = warmBiasIssueSite s.stage s.half ∨ 1353 ≤ s.issue := by
    fin_cases i <;> decide
  exact ⟨_,he,hs ▸ hh ▸ classify i⟩

private theorem biasPrimingFloor {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {a b : Event} (ha : X.get (g,i) = some a) (hb : X.get (g,j) = some b)
    (hA : a.pc < 780) (hB : 780 ≤ b.pc) : i < j := by
  apply Thread.traceOrderOfPcFloor hX (floor := 780) _ _ ha hb hA hB
  all_goals set_option maxRecDepth 100000 in kernel_rfl

private theorem biasTailFloor {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {a b : Event} (ha : X.get (g,i) = some a) (hb : X.get (g,j) = some b)
    (hA : a.pc < 1353) (hB : 1353 ≤ b.pc) : i < j := by
  apply Thread.traceOrderOfPcFloor hX (floor := 1353) _ _ ha hb hA hB
  all_goals set_option maxRecDepth 100000 in kernel_rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The first recorded Bias issue of a half has physical generation zero. -/
theorem biasPrimingOrdinalZero (stage half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
    (he : X.get (g,j) =
      some ⟨(inputSite (firstBiasIssueSite stage half)).pc,.tensorIssue p.biasMapAddress spec⟩) :
    biasTensorOrdinal l X stage half (g,j) = 0 := by
  by_contra! hNonZero
  obtain ⟨k,hBefore,b,hBox,_⟩ := biasEarlierHalfOfOrdinal hp hX
    (g := g) (j := j) (stage := stage) (half := half) (n := 0) (by omega)
  obtain ⟨source,hGet,hCase⟩ := earlierBiasSource hp hX hBox
  rcases hCase with hPrime | hWarm | hTail
  · subst source
    have heq := primingBiasIssueOnceInLane hX stage half hGet he
    omega
  · subst source
    have hLo : (inputSite (firstBiasIssueSite stage half)).pc < 780 := by
      fin_cases stage <;> fin_cases half <;> decide
    have hHi : 780 ≤ warmBiasIssueSite stage half := by
      fin_cases stage <;> fin_cases half <;> decide
    have h := biasPrimingFloor hX he hGet hLo hHi
    omega
  · have hLo : (inputSite (firstBiasIssueSite stage half)).pc < 780 := by
      fin_cases stage <;> fin_cases half <;> decide
    have h := biasPrimingFloor hX he hGet hLo (show 780 ≤ source by omega)
    omega

private theorem biasOrderStrict {g i j : Nat} {stage half : Fin 2} {a b : TensorCopy.Spec}
    (hi : BiasSubbox p l X (g,i) stage half a) (hj : BiasSubbox p l X (g,j) stage half b)
    (hOrder : i < j) :
    biasTensorOrdinal l X stage half (g,i) < biasTensorOrdinal l X stage half (g,j) := by
  have hLe := countP_take_mono (biasTensorHalf l (g/l.block) stage half) (X.tr g) hOrder.le
  apply lt_of_le_of_ne hLe
  intro hSame
  have hEq := congrArg Prod.snd (biasTensorOrdinalInjective hp hX hi hj rfl hSame)
  exact (Nat.ne_of_lt hOrder) hEq

private theorem warmOrdinalAtLeast (stage half : Fin 2) {g j rank round : Nat}
    {spec : TensorCopy.Spec} (hBox : BiasSubbox p l X (g,j) stage half spec)
    (he : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress spec⟩)
    (hRank : ((X.tr g).take j).countP Execution.isShfl = rank+64*round+32)
    (hEarlier : ∀ prior < round, ∃ k < j, ∃ box, BiasSubbox p l X (g,k) stage half box ∧
      X.get (g,k) = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress box⟩ ∧
      ((X.tr g).take k).countP Execution.isShfl = rank+64*prior+32) :
    round+1 ≤ biasTensorOrdinal l X stage half (g,j) := by
  have counts (i : Nat) (hi : i ≤ round) {k : Nat} {box : TensorCopy.Spec}
      (hB : BiasSubbox p l X (g,k) stage half box)
      (hE : X.get (g,k) = some
        ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress box⟩)
      (hR : ((X.tr g).take k).countP Execution.isShfl = rank+64*i+32) :
      i+1 ≤ biasTensorOrdinal l X stage half (g,k) := by
    induction i generalizing k box with
    | zero =>
      have hLate : 780 ≤ warmBiasIssueSite stage half := by
        fin_cases stage <;> fin_cases half <;> decide
      obtain ⟨pre,hPrior,pbox,hPrime⟩ := primingBiasEarlierThanRepeated hp hX hB hE hLate
      have hOrd := biasOrderStrict hp hX hPrime hB hPrior
      omega
    | succ i ih =>
      obtain ⟨prev,_,box',hPrev,hPrevious,hCount⟩ := hEarlier i (by omega)
      have hOrder : prev < k := by
        by_contra! h
        have hMono := countP_take_mono Execution.isShfl (X.tr g) h
        omega
      have hPrevOrd := ih (by omega) hPrev hPrevious hCount
      have hLarger := biasOrderStrict hp hX hPrev hB hOrder
      omega
  exact counts round le_rfl hBox he hRank

private theorem warmOrdinalAtMost (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    (stage half : Fin 2) {g batch j round : Nat} {spec : TensorCopy.Spec} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hBox : BiasSubbox p l X (g,j) stage half spec)
    (he : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress spec⟩)
    (hRank : ((X.tr g).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch+64+64*round+32) :
    biasTensorOrdinal l X stage half (g,j) ≤ round+1 := by
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨owner,_,hOwner⟩ := tileBatch_existsUnique p hActive
  generalize hOrdinal : biasTensorOrdinal l X stage half (g,j) = n
  induction n using Nat.strong_induction_on generalizing j round spec with
  | h n ih =>
    by_cases hZero : n = 0
    · omega
    obtain ⟨k,hBefore,earlier,hEarlier,hNumber⟩ :=
      biasEarlierHalfOfOrdinal hp hX (g := g) (j := j) (stage := stage) (half := half)
        (n := n-1) (by omega)
    obtain ⟨pc,hGet,hClass⟩ := earlierBiasSource hp hX hEarlier
    rcases hClass with hPrime | hWarm | hTail
    · subst pc
      have hFirst := biasPrimingOrdinalZero hp hX stage half hGet
      omega
    · subst pc
      obtain ⟨other,ho,hOtherLo,hOtherHi,prev,hPrev,hPrevRank,_⟩ :=
        warmBiasRoundsOfIssue hp hX hFrame hCuQ stage half hEarlier hGet
      have heq := (hOwner other ⟨ho,hOtherLo,hOtherHi⟩).trans
        (hOwner batch ⟨hb,hLo,hHi⟩).symm
      subst other
      have hLess : prev < round := by
        have hMono := countP_take_mono Execution.isShfl (X.tr g) hBefore.le
        have hNe : ((X.tr g).take k).countP Execution.isShfl ≠
            ((X.tr g).take j).countP Execution.isShfl := by
          intro hSame
          have hw := biasTensorActorWarp hp hX hBox
          exact (Nat.ne_of_lt hBefore)
            (warmBiasIssueUniqueAtRank hp hX hFrame stage half hw hActive hGet he hSame)
        omega
      have hSmaller := ih (n-1) (by omega) hEarlier hGet hPrevRank hNumber
      omega
    · have hWarm : warmBiasIssueSite stage half < 1353 := by
        fin_cases stage <;> fin_cases half <;> decide
      have hWrong := biasTailFloor hX he hGet hWarm hTail
      omega

/-- The actual warm issue's physical Bias generation is its traversal index plus
the priming packet, for every stage and half. -/
theorem warmBiasOrdinalExact (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    (stage half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
    (hBox : BiasSubbox p l X (g,j) stage half spec)
    (he : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress spec⟩) :
    ∃ batch < p.batch, tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      ∃ round < min (Mma.trips p batch tile-1) 9,
        ((X.tr g).take j).countP Execution.isShfl = primingSearchShuffleCount batch+64+64*round+32 ∧
        biasTensorOrdinal l X stage half (g,j) = round+1 := by
  obtain ⟨batch,hb,hLo,hHi,round,hRound,hRank,hEarlier⟩ :=
    warmBiasRoundsOfIssue hp hX hFrame hCuQ stage half hBox he
  have hUpper := warmOrdinalAtMost hp hX hFrame hCuQ stage half hb hLo hHi hBox he hRank
  have hLower := warmOrdinalAtLeast hp hX stage half hBox he hRank hEarlier
  exact ⟨batch,hb,hLo,hHi,round,hRound,hRank,Nat.le_antisymm hUpper hLower⟩

end PTX.Kernels.TmlFa4Fwd.Loader

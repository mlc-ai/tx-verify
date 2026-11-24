-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderTailBiasEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderBiasIssueExtent
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
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

set_option maxRecDepth 10000 in
/-- The optional low-stage Bias issue follows all nine warm boxes and the priming box. -/
theorem tailBiasOrdinalExact {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    (half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
    (hBox : BiasSubbox p l X (g,j) 0 half spec)
    (he : X.get (g,j) =
      some ⟨(inputSite (tailBiasInputSite half)).pc,.tensorIssue p.biasMapAddress spec⟩) :
    biasTensorOrdinal l X 0 half (g,j) = 10 := by
  let event : Event := ⟨(inputSite (tailBiasInputSite half)).pc,
    .tensorIssue p.biasMapAddress spec⟩
  let selector := warmBiasTensorSelector 0 half
  let lane := laneOf l g
  have hReal : X.get (g,j) = some event := he
  have hSafe : ∀ f, event.kind ≠ .ub f := by rintro _ ⟨⟩
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet : X.get (warpLane l g lane,j) = some event := hLane.symm ▸ he
  have hSite : 1353 ≤ event.pc ∧ event.pc < 1862 := by
    change 1353 ≤ (inputSite (tailBiasInputSite half)).pc ∧
      (inputSite (tailBiasInputSite half)).pc < 1862
    fin_cases half <;> decide
  have hActor := biasTensorActorWarp hp hX hBox
  have hActive := loaderOwnPrefixEventRequiresActiveTile hp hX hActor.ge hCuQ hReal
    (show 297 < event.pc by omega) hSite.2
  obtain ⟨batch,hb,hLo,hHi,hTrips,hResidue⟩ := tailBiasIssueTrips hp hX hCuQ half hBox he
  have hWarm : HasWarmTile p l g := ⟨batch,hb,hLo,hHi,by omega⟩
  obtain ⟨second,hsb,hSecondLo,hSecondHi,_,start,hStart,s,ending,hs,hr,hStartRank⟩ :=
    warmFirstWithBiasRoleOfEvent hp hX (src := lane) (event_thread_lt hX he) hActor.ge
      hLaneLt (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hGet (by omega)
      (.inr hWarm) hSafe
  obtain ⟨owner,_,hOwner⟩ := tileBatch_existsUnique p hActive
  have heq := (hOwner second ⟨hsb,hSecondLo,hSecondHi⟩).trans
    (hOwner batch ⟨hb,hLo,hHi⟩).symm
  subst second
  rw [hLane] at hs hr hStartRank
  let co := assignedCoordinates p batch (g/l.block)
  let trips := Mma.trips p batch co.1
  let F := [(2535,b32 l.sharedBase),(1062,b32 14),(123,.pred false)]
  have hHeld := hs.2.2.2.2
  have holds (r : Nat) (v : Value) (hm : (r,v) ∈
      warmStartFrame p l batch (co.2/6) trips (warpIndex l g) (g%l.block) ++
      warmBiasRoots p batch co.1 co.2 ++ [(123,.pred (decide (warpIndex l g ≠ 14)))]) :
      s.regs r = some v := holds_mem hHeld.2.2 hm
  have hs' : At s 917 ([(7174,b32 0),(1091,b32 (trips-1))] ++ F) := hs.mono
    ⟨hHeld.1,holds _ _ (by simp [warmStartFrame]),
      holds _ _ (by simp [warmStartFrame]),holds _ _ (by simp [warmStartFrame,hActor]),
      holds _ _ (by simp [hActor]),trivial⟩
  have hTrip : trips-1 < 2^31 := by
    have h := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
    have hLen := (hp.lengths batch hb).2.2
    change trips ≤ (p.kLength batch+127)/128 at h
    omega
  change 10 < trips at hTrips
  have hInit : 0 < min (trips-1) 9 := by omega
  have hAudit (n : Nat) : ((kernel.code.drop 917).take (1348-917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n ([7174,1091] ++ F.map Prod.fst) ins.op) =
      true := by set_option maxRecDepth 100000 in kernel_rfl
  have hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hShared : (2535,b32 l.sharedBase) ∈ F := by simp [F]
  have hWarp : (1062,b32 (14+(0 : Fin 2).val)) ∈ F := by simp [F]
  obtain ⟨pos,hPos,u,stop,_,hU,hRun,hCount⟩ :=
    warmObservedIterations (hops := 8) 0 hTrip hInit hShared hWarp hAudit hTail
      hs' hr hReal hStart (.inl (by omega)) hSafe (.inl (by omega))
  obtain ⟨tail,_ ,_,hTailIssue⟩ := biasTensorSelectorOfSubbox hp hX hBox
  obtain ⟨k,_,inst,hKnown⟩ := biasTensorActualElection hp hX tail hTailIssue
  have hRole : At u 917 [(123,.pred false)] := hU.mono
    ⟨holds_mem hU.2.2.2.2.2.2 (by simp [F]),trivial⟩
  have hBelow : (biasTensorSelector selector).issue < 1353 := by fin_cases half <;> decide
  have hLater : (biasTensorSelector selector).issue ≤ event.pc := by omega
  obtain ⟨index,hBefore,address,a,hIssue,hRank⟩ :=
    warmSelectedBiasIssueBeforeTensor hX (0 : Fin 2) half hKnown hRole hRun hReal hPos hLater
  have hStrict : index < j := by
    apply Thread.traceOrderOfPcFloor hX (floor := 1353) _ _ hIssue hReal hBelow hSite.1
    all_goals set_option maxRecDepth 100000 in kernel_rfl
  let site := (biasTensorSelector selector).input
  have hB : (inputSite site).bias = true := by fin_cases half <;> decide
  have hOff : (inputSite site).sharedOffset = 166912+16384*half.val := by fin_cases half <;> decide
  have hOffset : inputBarrierBase site+(inputSite site).barrierOffset = 320 := by
    fin_cases half <;> decide
  obtain ⟨hAddr,hMap,hRows,hDst,hCluster,hGroup⟩ := actualInputBoxAt hp hX site hIssue
  have hMbar := loaderTensorOffset hp hX site hIssue
  rw [hOffset] at hMbar
  rw [hOff] at hDst
  rw [inputMapAddress,hB] at hAddr
  rw [inputMap,hB] at hMap
  subst address
  have hEarlier : BiasSubbox p l X (g,index) 0 half a :=
    ⟨⟨_,hIssue⟩,hMbar,hDst,hMap,hRows,hCluster,hGroup⟩
  have hSel : (biasTensorSelector selector).issue = warmBiasIssueSite 0 half := by
    fin_cases half <;> decide
  have hWarmIssue : X.get (g,index) = some
      ⟨warmBiasIssueSite 0 half,.tensorIssue p.biasMapAddress a⟩ := by
    rw [← hSel]
    exact hIssue
  obtain ⟨another,hAnother,hAnotherLo,hAnotherHi,round,_,hRoundRank,hPhase⟩ :=
    warmBiasOrdinalExact hp hX hFrame hCuQ 0 half hEarlier hWarmIssue
  have hSame := (hOwner another ⟨hAnother,hAnotherLo,hAnotherHi⟩).trans
    (hOwner batch ⟨hb,hLo,hHi⟩).symm
  subst another
  rw [hCount,hStartRank] at hRank
  have hRoundEight : round = 8 := by omega
  subst round
  have hGrow := countP_take_mono (biasTensorHalf l (g/l.block) 0 half) (X.tr g) hStrict.le
  have hLt : biasTensorOrdinal l X 0 half (g,index) < biasTensorOrdinal l X 0 half (g,j) := by
    apply lt_of_le_of_ne hGrow
    intro heq'
    exact (Nat.ne_of_lt hStrict)
      (congrArg Prod.snd (biasTensorOrdinalInjective hp hX hEarlier hBox rfl heq'))
  obtain ⟨any,_,_,_,hBound⟩ := biasTensorOrdinalWithinBudget hp hX hCuQ hBox
  have hMax : biasLoaderBudget p any (assignedCoordinates p any (g/l.block)).1 0 ≤ 11 := by
    unfold biasLoaderBudget biasTailExtra
    split <;> omega
  change biasTensorOrdinal l X 0 half (g,j) <
    biasLoaderBudget p any (assignedCoordinates p any (g/l.block)).1 0 at hBound
  rw [hPhase] at hLt
  omega

end PTX.Kernels.TmlFa4Fwd.Loader

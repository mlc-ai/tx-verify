-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmIterationCursor
public import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
public import Kernels.TmlFa4Fwd.Proof.LoaderBiasWarmCount
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates
import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue Thread.Loader

set_option maxRecDepth 10000 in
/-- A real warm Bias issue identifies the actual traversal and its shuffle ordinal.
On the same issuer, each preceding traversal already supplied this stage and half. -/
theorem warmBiasRoundsOfIssue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    (stage half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
    (hBox : BiasSubbox p l X (g,j) stage half spec)
    (he : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let base := primingSearchShuffleCount batch + 64
      ∃ round < min (Mma.trips p batch tile-1) 9,
        ((X.tr g).take j).countP Execution.isShfl = base+64*round+32 ∧
        ∀ prior < round, ∃ issue < j, ∃ a,
          BiasSubbox p l X (g,issue) stage half a ∧
          X.get (g,issue) = some
            ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress a⟩ ∧
          ((X.tr g).take issue).countP Execution.isShfl = base+64*prior+32 := by
  let target : Event := ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress spec⟩
  let selector := warmBiasTensorSelector stage half
  let lane := laneOf l g
  have hSafe : ∀ f, target.kind ≠ .ub f := by rintro _ ⟨⟩
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet : X.get (warpLane l g lane,j) = some target := hLane.symm ▸ he
  have hSite : 917 ≤ target.pc ∧ target.pc < 1348 := by
    change 917 ≤ warmBiasIssueSite stage half ∧ warmBiasIssueSite stage half < 1348
    fin_cases stage <;> fin_cases half <;> decide
  have hSelector : (biasTensorSelector selector).issue = target.pc := by
    change (biasTensorSelector selector).issue = warmBiasIssueSite stage half
    fin_cases stage <;> fin_cases half <;> decide
  have he' : X.get (g,j) = some ⟨(biasTensorSelector selector).issue,
      .tensorIssue p.biasMapAddress spec⟩ := by rw [hSelector]; exact he
  have hActor := biasTensorActorWarp hp hX hBox
  have hReal : X.get (g,j) = some target := he
  have hActive := loaderOwnPrefixEventRequiresActiveTile hp hX hActor.ge hCuQ hReal
    (show 297 < target.pc by omega) (show target.pc < 1862 by omega)
  obtain ⟨batch,hb,hLo,hHi,hTwo,start,hStart,s,ending,hs,hr,hStartRank⟩ :=
    warmFirstWithBiasRoleOfEvent hp hX (src := lane) (event_thread_lt hX he) hActor.ge
      hLaneLt (fun _ _ _ _ => loaderOutputWrites hFrame) hActive hGet hSite.1
      (.inl (by omega)) hSafe
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
  change 2 ≤ trips at hTwo
  have hInit : 0 < min (trips-1) 9 := by omega
  have hAudit (n : Nat) : ((kernel.code.drop 917).take (1348-917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n ([7174,1091] ++ F.map Prod.fst) ins.op) =
      true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hShared : (2535,b32 l.sharedBase) ∈ F := by simp [F]
  have hWarp : (1062,b32 (14+(0 : Fin 2).val)) ∈ F := by simp [F]
  have hRemainder : loaderShuffleTail 1348 target.pc = 32 := by
    change loaderShuffleTail 1348 (warmBiasIssueSite stage half) = 32
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨round,_,hRound,hRank⟩ :=
    warmRoundOfObservedEvent 0 hTrip hInit hShared hWarp hAudit hTail hs' hr hReal hStart
      hSite.2 hSafe
  rw [hRemainder,Nat.sub_zero,hStartRank] at hRank
  refine ⟨batch,hb,hLo,hHi,round,hRound,by omega,?_⟩
  intro prior hPrior
  have hEnough : ((X.tr g).take start).countP Execution.isShfl +64*prior <
      ((X.tr g).take j).countP Execution.isShfl := by rw [hStartRank]; omega
  obtain ⟨pos,hPos,u,stop,_,hU,hRun,hCount⟩ :=
    warmObservedIterations (hops := prior) 0 hTrip hInit hShared hWarp hAudit hTail
      hs' hr hReal hStart (.inl (by omega)) hSafe (.inr hEnough)
  obtain ⟨k,_,inst,hKnown⟩ := biasTensorActualElection hp hX selector he'
  have hRole : At u 917 [(123,.pred false)] := hU.mono
    ⟨holds_mem hU.2.2.2.2.2.2 (by simp [F]),trivial⟩
  obtain ⟨issue,hBefore,address,a,hIssue,hShfl⟩ :=
    warmSelectedBiasIssue hX stage half hKnown hRole hRun he' hPos
  rw [hCount,hStartRank] at hShfl
  have hLt : issue < j := by
    by_contra! hEq
    have hMono := countP_take_mono Execution.isShfl (X.tr g) hEq
    omega
  let site := (biasTensorSelector selector).input
  have hB : (inputSite site).bias = true := by fin_cases stage <;> fin_cases half <;> decide
  have hOff : (inputSite site).sharedOffset = 166912+32768*stage.val+16384*half.val := by
    fin_cases stage <;> fin_cases half <;> decide
  have hOffset : inputBarrierBase site+(inputSite site).barrierOffset = 320+8*stage.val := by
    fin_cases stage <;> fin_cases half <;> decide
  obtain ⟨hAddr,hMap,hRows,hDst,hCluster,hGroup⟩ := actualInputBoxAt hp hX site hIssue
  have hMbar := loaderTensorOffset hp hX site hIssue
  rw [hOffset] at hMbar
  rw [hOff] at hDst
  rw [inputMapAddress,hB] at hAddr
  rw [inputMap,hB] at hMap
  subst address
  refine ⟨issue,hLt,a,⟨⟨_,hIssue⟩,hMbar,hDst,hMap,hRows,hCluster,hGroup⟩,?_,by omega⟩
  rw [hSelector] at hIssue
  exact hIssue

end PTX.Kernels.TmlFa4Fwd.Loader

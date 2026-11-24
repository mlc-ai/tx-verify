-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmStartInPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Kernels.TmlFa4Fwd.Proof.LoaderBiasTailGuard
import Kernels.TmlFa4Fwd.Proof.LoaderBiasIssueExtent
import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry
import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The two Bias input sites in the optional low-stage packet. -/
def tailBiasInputSite (half : Fin 2) : Fin 14 := ⟨12+half.val,by have := half.isLt; omega⟩

set_option maxRecDepth 10000 in
/-- An actual optional Bias issue sees the selected packed row and head together
with the decoded steady counter bounded by the warm length. -/
theorem tailBiasEntryOfIssue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    (half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
    (hBox : Thread.Loader.BiasSubbox p l X (g,j) 0 half spec)
    (he : X.get (g,j) =
      some ⟨(inputSite (tailBiasInputSite half)).pc,.tensorIssue p.biasMapAddress spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      let trips := Mma.trips p batch co.1
      ∃ pos ≤ j, ∃ t ending,
        At t 1355 [(7181,b32 (min (trips-1) 9)),(1062,b32 14),(2535,b32 l.sharedBase),
          (1087,b32 (p.qOffset batch+256*co.1)),(7169,b32 co.2)] ∧
        Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending := by
  have hw := biasTensorActorWarp hp hX hBox
  let pc := (inputSite (tailBiasInputSite half)).pc
  let target : Event := ⟨pc,.tensorIssue p.biasMapAddress spec⟩
  have hGet : X.get (g,j) = some target := he
  have hLate : 1355 ≤ target.pc ∧ target.pc < 1384 := by
    change 1355 ≤ (inputSite (tailBiasInputSite half)).pc ∧
      (inputSite (tailBiasInputSite half)).pc < 1384
    fin_cases half <;> decide
  have hActive := loaderOwnPrefixEventRequiresActiveTile hp hX hw.ge hCuQ hGet (by omega)
    (by omega)
  let lane := laneOf l g
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hSafe : ∀ f, target.kind ≠ .ub f := by rintro _ ⟨⟩
  obtain ⟨batch,hb,hLo,hHi,start,hStart,s,ending,hs,hr,_⟩ :=
    loaderWarmStartWithBiasOfEvent hp hX (src := lane) (event_thread_lt hX he) hw.ge hLaneLt
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hActive (hLane.symm ▸ hGet)
      (by omega) hSafe
  rw [hLane] at hr
  let co := assignedCoordinates p batch (g/l.block)
  let trips := Mma.trips p batch co.1
  let F := [(1091,b32 (trips-1)),(1062,b32 14),(2535,b32 l.sharedBase),
    (1087,b32 (p.qOffset batch+256*co.1)),(7169,b32 co.2)]
  have hsF : At s 907 F := by
    apply hs.mono
    have hHeld := hs.2.2.2.2
    refine ⟨holds_mem hHeld ?_,holds_mem hHeld ?_,holds_mem hHeld ?_,
      holds_mem hHeld ?_,holds_mem hHeld ?_,trivial⟩
    all_goals simp [warmStartFrame,warmBiasRoots,co,trips,hw]
  have hAudit (bound : Nat) : ((kernel.code.drop 907).take (1353-907)).all
      (fun ins => loaderPipelineCutOp 907 1353 bound (F.map Prod.fst) ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨a,pos,ending,hA,hRun,hPos⟩ :=
    observedBiasCut (start := 907) (stop := 1353) (by decide) hsF hAudit hr hGet hStart
      (by omega) hSafe
  obtain ⟨hTile,_⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrips := (Mma.trips_bounds hp hb hTile).2.1
  have hLength := (hp.lengths batch hb).2.2
  change trips ≤ (p.kLength batch+127)/128 at hTrips
  have hBound : trips-1 < 2^31 := by omega
  obtain ⟨b,hbCore,hB⟩ := (loaderSteadyCounterInitCore (l := l) (g := g) hBound).apply
    (hA.mono ⟨hA.2.2.2.2.1,trivial⟩)
  obtain ⟨hbStep,hFrame'⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hA.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hbCore
  have hOut := holdsSchedulerFrame hA.2.2.2.2 hFrame' (fun _ hm => List.mem_map_of_mem hm)
  have hAfter := hRun.after_local_nonempty (run_rtg hbStep) (traceAfterObservedEvent hGet hPos)
  exact ⟨batch,hb,hLo,hHi,pos,hPos,b,ending,hB.mono
    ⟨hB.2.2.2.2.1,hOut.2.1,hOut.2.2.1,hOut.2.2.2.1,hOut.2.2.2.2.1,trivial⟩,hAfter⟩

/-- A realized tail requires ten earlier visits and a distinct low-stage causal end. -/
theorem tailBiasIssueTrips {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X)
    (half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
    (hBox : Thread.Loader.BiasSubbox p l X (g,j) 0 half spec)
    (he : X.get (g,j) =
      some ⟨(inputSite (tailBiasInputSite half)).pc,.tensorIssue p.biasMapAddress spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      10 < Mma.trips p batch tile ∧ vPrimingResidual p batch tile ≠ 0 := by
  let event : Event := ⟨(inputSite (tailBiasInputSite half)).pc,
    .tensorIssue p.biasMapAddress spec⟩
  have hAt : 1376 ≤ event.pc ∧ event.pc < 1384 := by
    change 1376 ≤ (inputSite (tailBiasInputSite half)).pc ∧
      (inputSite (tailBiasInputSite half)).pc < 1384
    fin_cases half <;> decide
  have hGet : X.get (g,j) = some event := he
  have hw := biasTensorActorWarp hp hX hBox
  obtain ⟨batch,hb,hLo,hHi,pos,s,out,hPos,hFrame,hRun⟩ :=
    biasTripFrameOfEvent hp hX hCuQ hw hGet (by omega)
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let trips := Mma.trips p batch tile
  let residue := vPrimingResidual p batch tile
  obtain ⟨hTile,_⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrip := (Mma.trips_bounds hp hb hTile).2.1
  have hLength := (hp.lengths batch hb).2.2
  change trips ≤ (p.kLength batch+127)/128 at hTrip
  have hTripFit : trips < 2^31 := by omega
  have hResidue : residue < 2^32 := Nat.mod_lt _ (by decide)
  have hSafe : ∀ f, event.kind ≠ .ub f := by rintro _ ⟨⟩
  exact ⟨batch,hb,hLo,hHi,
    biasTailGuardOfPrimingFrame hTripFit hResidue (hFrame.mono
      ⟨hFrame.2.2.2.2.1,hFrame.2.2.2.2.2.1,hFrame.2.2.2.2.2.2.1,trivial⟩)
      hRun hGet hPos hAt hSafe⟩

end PTX.Kernels.TmlFa4Fwd.Loader

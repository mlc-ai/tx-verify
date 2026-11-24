-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingBiasOrder
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingInputCursor
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Flow.Code.Part021

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue Thread.Loader

def singleVisitRoots (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

def singleVisitTrip (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  (1088, b32 1) :: (1091, b32 0) :: singleVisitRoots l warp

private theorem singleVisitWarmFlags {l : Launch} {g : Nat} (warp : Fin 2) (flag : Bool) :
    Seg kernel [] l g 6 905 ((164, .pred flag) :: singleVisitTrip l warp) 911
      ((166, .pred true) :: (7, .pred false) :: (1091, b32 0) :: singleVisitRoots l warp) := by
  intro s hs
  simp only [singleVisitTrip, singleVisitRoots] at hs ⊢
  seg_fp hs using rfl

private theorem singleVisitSteadyFlags {l : Launch} {g : Nat} (warp : Fin 2) :
    Seg kernel [] l g 5 1353
      ((7, .pred false) :: (1091, b32 0) :: singleVisitRoots l warp) 1358
      ((202, .pred true) :: (7181, b32 0) :: (1091, b32 0) :: singleVisitRoots l warp) := by
  intro s hs
  fin_cases warp <;> (simp only [singleVisitRoots] at hs ⊢; seg_fp hs using rfl)

private theorem singleVisitDrainFlags {l : Launch} {g : Nat} (warp : Fin 2) :
    Seg kernel [] l g 1 1384
      ((7181, b32 0) :: (1091, b32 0) :: singleVisitRoots l warp) 1385
      ((209, .pred true) :: singleVisitRoots l warp) := by
  intro s hs
  simp only [singleVisitRoots] at hs ⊢
  seg_fp hs using rfl

/-- With one visible trip the loader skips both warm Bias expectations and the final
extra Bias expectation. All three decisions are local and preserve the actual event suffix. -/
theorem singleVisitBiasBypass {l : Launch} {g : Nat} (warp : Fin 2) (flag : Bool) :
    Seg kernel Assumptions.all l g 15 905 ((164, .pred flag) :: singleVisitTrip l warp) 1744
      (singleVisitRoots l warp) := by
  intro s hs
  have hWarmBranch : Seg kernel [] l g 1 911
      ((166, .pred true) :: (7, .pred false) :: (1091, b32 0) :: singleVisitRoots l warp) 1353
      ((166, .pred true) :: (7, .pred false) :: (1091, b32 0) :: singleVisitRoots l warp) :=
    Seg.bra (A := []) (pick := true) Flow.code_911 (by simp)
      (fun _ _ _ h => (List.not_mem_nil h).elim)
  obtain ⟨t, ht, hT⟩ := ((singleVisitWarmFlags warp flag).comp hWarmBranch).apply hs
  have htA := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) ht).1
  have hSteadyBranch : Seg kernel [] l g 1 1358
      ((202, .pred true) :: (7181, b32 0) :: (1091, b32 0) :: singleVisitRoots l warp) 1384
      ((202, .pred true) :: (7181, b32 0) :: (1091, b32 0) :: singleVisitRoots l warp) :=
    Seg.bra (A := []) (pick := true) Flow.code_1358 (by simp)
      (fun _ _ _ h => (List.not_mem_nil h).elim)
  obtain ⟨u, hu, hU⟩ := ((singleVisitSteadyFlags warp).comp hSteadyBranch).apply
    (hT.mono hT.2.2.2.2.2)
  have huA := (loaderLinear (regs := []) (by decide) (by decide) hT.1
    (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) hu).1
  have hDrainBranch : Seg kernel [] l g 1 1385
      ((209, .pred true) :: singleVisitRoots l warp) 1744
      ((209, .pred true) :: singleVisitRoots l warp) :=
    Seg.bra (A := []) (pick := true) Flow.code_1385 (by simp)
      (fun _ _ _ h => (List.not_mem_nil h).elim)
  obtain ⟨v, hv, hV⟩ := ((singleVisitDrainFlags warp).comp hDrainBranch).apply
    (hU.mono hU.2.2.2.2.2)
  have hvA := (loaderLinear (regs := []) (by decide) (by decide) hU.1
    (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) hv).1
  exact ⟨v, run_comp (run_comp htA huA) hvA, hV.mono hV.2.2.2.2.2⟩

private theorem singleVisitTailCode (bound : Nat) :
    ((kernel.code.drop 1744).take (1901 - 1744)).all
      (fun i => loaderPipelineCutOp 1744 1901 bound [2535, 1062] i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem singleVisitResidualFlag {p : Params} {l : Launch} {g batch tile : Nat}
    (warp : Fin 2) :
    let residual := vPrimingResidual p batch tile
    Seg kernel [] l g 1 803 ((1089, b32 residual) :: singleVisitTrip l warp) 804
      ((164, .pred (residual != 0)) :: singleVisitTrip l warp) := by
  dsimp only
  rcases firstBiasResidual p batch tile with h | h <;> rw [h]
  all_goals
    intro s hs
    simp only [singleVisitTrip, singleVisitRoots] at hs ⊢
    seg_fp hs using rfl

/-- The live one-trip cursor excludes the recurring section from the actual loader trace.
The residual predicate and both bypasses are reconstructed from decoded instructions. -/
theorem singleVisitNoRecurringBiasFromAdmission {p : Params} {l : Launch}
    {g batch tile : Nat} {s : TState} {events : List Event} {visits : List Visit} (warp : Fin 2)
    (hs : At s 488 ((1089, b32 (vPrimingResidual p batch tile)) :: singleVisitTrip l warp))
    (hw : Walk kernel Assumptions.all l g s events visits) {e : Event}
    (hLo : 905 ≤ e.pc) (hHi : e.pc < 1744) (hCont : ¬ Ends e) :
    e ∉ events := by
  intro hE
  let residual := vPrimingResidual p batch tile
  let F := (1089, b32 residual) :: singleVisitTrip l warp
  let G := (164, .pred (residual != 0)) :: singleVisitTrip l warp
  have hS := loaderEventInClosedSlice warp (by decide) (by decide) singleVisitTailCode hw
    (by rw [hs.1]; decide) (ringShapeOfAt hs) hs.2.2.2.2.2.2.2 hE hHi
  have hCode : ((kernel.code.drop 488).take (803 - 488)).all
      (fun i => loaderPipelineCutOp 488 803 (1744 - 1) [1089, 1088, 1091, 2535, 1062] i.op)
        = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t, _, rest, _, post, _, _, _, ht, hShape, hFrame, _, hRest, hSaw⟩ :=
    loaderObservedCut (F := F) (by decide) (by decide) (by decide : 803 ≤ 1901)
      (by decide : 803 < 1744) hCode hw (by rw [hs.1]; decide) (ringShapeOfAt hs)
      hs.2.2.2.2 hS (by omega) hCont
  have hMem := memEventsOfLoaderSlice hRest hSaw
  have hT : At t 803 F := pipelineAtCut ht hShape hFrame
    (walkWithContinuingEventClean hRest hMem hCont) ⟨_, Flow.code_803, rfl⟩
  obtain ⟨u, hu, hU⟩ :=
    (singleVisitResidualFlag (g := g) (p := p) (batch := batch) (tile := tile) warp).apply hT
  have huA := (loaderLinear (regs := []) (by decide) (by decide) hT.1 (by simp) rfl hu).1
  obtain ⟨_, hTail⟩ := loaderWalkAfterLocals hRest (List.ne_nil_of_mem hMem) (run_rtg huA)
  have hUS := loaderEventInClosedSlice warp (by decide) (by decide) singleVisitTailCode hTail
    (by rw [hU.1]; decide) (ringShapeOfAt hU) hU.2.2.2.2.2.2.2 hMem hHi
  have hCode : ((kernel.code.drop 804).take (905 - 804)).all
      (fun i => loaderPipelineCutOp 804 905 (1744 - 1) [164, 1088, 1091, 2535, 1062] i.op)
        = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v, _, remaining, _, post, _, _, _, hv, hShape, hFacts, _, hTail, hSeen⟩ :=
    loaderObservedCut (F := G) (by decide) (by decide) (by decide : 905 ≤ 1901)
      (by decide : 905 < 1744) hCode hTail (by rw [hU.1]; decide) (ringShapeOfAt hU)
      hU.2.2.2.2 hUS hLo hCont
  have hMem := memEventsOfLoaderSlice hTail hSeen
  have hV : At v 905 G := pipelineAtCut hv hShape hFacts
    (walkWithContinuingEventClean hTail hMem hCont) ⟨_, Flow.code_905, rfl⟩
  obtain ⟨w, hwLocal, hW⟩ := (singleVisitBiasBypass (g := g) warp (residual != 0)).rtg hV
  obtain ⟨_, hFinal⟩ := loaderWalkAfterLocals hTail (List.ne_nil_of_mem hMem) hwLocal
  have hFloor := (loaderWalkEventRange warp (by decide) (by rw [hW.1]; decide)
    (ringShapeOfAt hW) hW.2.2.2.2 singleVisitTailCode hFinal e hMem).1
  omega

/-- No active one-trip loader emits a continuing event in the recurring input interval. -/
theorem singleVisitLoaderEventNotRecurring {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g index batch : Nat}
    (hb : batch < p.batch) (hLow : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHigh : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    {event : Event} (he : X.get (g, index) = some event)
    (hBounds : 905 ≤ event.pc ∧ event.pc < 1744) (hContinue : ¬ Ends event) : False := by
  obtain ⟨warp, t, pos, hAt, hRun, hPos⟩ :=
    primingInputCursorBeforePacketEvent hp hX hComplete hb hLow hHigh writes he
      ⟨(by decide : 515 ≤ 905).trans hBounds.1, hBounds.2⟩
  let coords := assignedCoordinates p batch (g / l.block)
  have hInTrace : event ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := index - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  have existsFrame :
      At t 488 ((1089, b32 (vPrimingResidual p batch coords.1)) :: singleVisitTrip l warp) := by
    apply hAt.mono
    simp only [singleVisitTrip, singleVisitRoots, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | (apply holds_mem hAt.2.2.2.2
         simp [coords, primingInputCursorFrame, primingVTripFrame, hTrip])
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRun
  exact singleVisitNoRecurringBiasFromAdmission warp existsFrame hWalk hBounds.1 hBounds.2
    hContinue hInTrace

/-- Every input TMA issue of an active, single-visit CTA belongs to its priming packet. -/
theorem singleVisitInputIssueIsPriming {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g index pc address batch : Nat} {spec : TensorCopy.Spec}
    (hb : batch < p.batch) (hLow : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHigh : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (he : X.get (g, index) = some ⟨pc, .tensorIssue address spec⟩) :
    pc < 780 := by
  by_contra! hLate
  let event : Event := ⟨pc, .tensorIssue address spec⟩
  obtain ⟨site, hSite⟩ := actualInputIssuePc hX he
  have hBounds : 905 ≤ pc ∧ pc < 1744 := by
    rw [hSite] at hLate ⊢
    fin_cases site <;> dsimp [inputSite] at hLate ⊢ <;> omega
  exact singleVisitLoaderEventNotRecurring hp hX hComplete hb hLow hHigh hTrip writes he
    (show 905 ≤ event.pc ∧ event.pc < 1744 from hBounds) (by simp [Ends])

open Protocol.Bias Thread.Scores in
/-- With one visit, the actual first Bias acquire selects the two priming notifications,
indexed by their physical half. -/
theorem singleVisitFirstBiasBoxes {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {batch g wait : Nat} {stage : Fin 2}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hWait : FirstBiasAcquire l X g wait stage) :
    ∃ phase, FirstBiasAcquirePhase l X g wait stage phase ∧
      ∃ tensor : Fin 2 → EvId, ∃ boxes : Fin 2 → TensorCopy.Observation,
        ∀ half, BiasNotifyPhase l X g stage phase (tensor half) ∧
          AcquiredBiasBox p l X stage g wait (tensor half) half (boxes half) := by
  obtain ⟨phase, _, hPhase⟩ := firstBiasAcquirePhase hp hX hWait
  refine ⟨phase, hPhase, firstBiasAcquiredPrimingHalves hp hX hWait hPhase ?_⟩
  intro tensor hNote
  obtain ⟨half, o, hBox⟩ := acquiredBiasBoxOfNotification hp hX hWait hPhase hNote
  obtain ⟨pc, he⟩ := hBox.issue
  obtain ⟨producer, index⟩ := tensor
  have hOwner : producer / l.block = g / l.block := hBox.owner
  exact ⟨_, he, singleVisitInputIssueIsPriming hp hX hComplete hb (hOwner.symm ▸ hLo)
    (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrip) writes he⟩

end PTX.Kernels.TmlFa4Fwd.Loader

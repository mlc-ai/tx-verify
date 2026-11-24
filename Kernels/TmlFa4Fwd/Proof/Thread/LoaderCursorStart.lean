-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorTrace
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
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

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open Prologue (warpIndex)
open PTX.Kernels.TmlFa4Fwd.Loader
  (pipelineAtCut ringShapeOfAt walkWithContinuingEventClean)

set_option maxRecDepth 100000 in
private theorem loaderDrainFloor :
    (kernel.code.drop 1744).all (fun ins => staysPastEvent 1744 ins.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem loaderDrainSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (1744 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem recurringWalkThroughEvent {l : Launch} {g : Nat} {t : TState}
    {history : List Event} {visits : List Visit} {i : Nat} {e : Event}
    (ht : At t 909 [(2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g t history visits)
    (he : history[i]? = some e) (hBound : e.pc < 1744) :
    ∃ before, Walk kernel Assumptions.all l g t (history.take (i + 1)) before ∧
      ∀ v ∈ before, 909 ≤ v.pc ∧ v.pc < 1744 := by
  let route := CursorRoute.throughReuse
  have hin : route.inside t.pc = true := by rw [ht.1]; decide
  have hStay {es : List Event} {trail : List Visit}
      (hWalk : Walk kernel Assumptions.all l g t es trail)
      (hInside : ∀ v ∈ trail, route.inside v.pc = true) :
      ∃ before, Walk kernel Assumptions.all l g t (es.take (i + 1)) before ∧
        ∀ v ∈ before, 909 ≤ v.pc ∧ v.pc < 1744 := by
    obtain ⟨before, hPrefix, hCut⟩ := takeLoaderEvents hWalk (i + 1)
    exact ⟨before, hCut, fun v hv => of_decide_eq_true (hInside v (hPrefix.subset hv))⟩
  rcases route.cutWalk hw hin (ringShapeOfAt ht) with hInside |
    ⟨u, before, after, earlier, later, hSplit, _, hBefore, hDrain, _, _, hInitial, hAfter⟩
  · exact hStay hw hInside
  have hStop : u.pc = 1744 := by simpa [route, CursorRoute.stops] using hDrain
  have hEarlier : i < before.length := by
    by_contra! hLate
    rw [hSplit, List.getElem?_append_right hLate] at he
    have hLatePc := eventTailEvents loaderDrainFloor loaderDrainSegments hAfter
      hStop.ge e (List.mem_of_getElem? he)
    omega
  rw [hSplit, List.take_append_of_le_length (by omega : i + 1 ≤ before.length)]
  exact hStay hInitial hBefore

/-- The actual recurring loader suffix starts at the unique seed cut. Every
event before the cut is from the common startup or one of the priming packets. -/
theorem actualCursorSeedPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hContinues : ¬ Ends e) (hBand : 909 ≤ e.pc ∧ e.pc < 1744) :
    ∃ (start : Nat) (s : TState) (visits : List Visit),
      start ≤ index ∧ (∀ event ∈ (X.tr g).take start, event.pc < 909) ∧
      At s 909 [(2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s (((X.tr g).drop start).take (index - start + 1)) visits ∧
      (∀ v ∈ visits, v.pc < 1744) := by
  have hLate : 173 < e.pc := by omega
  have hHint : e.pc ∉ registerHintSites := by simp [registerHintSites]; omega
  have hWarp : 14 ≤ warpIndex l g := by
    rcases roleBodyPcOfEvent hp hX he hLate hHint with h | h
    · omega
    · split_ifs at h <;> omega
  have hg : g < l.threads := event_thread_lt hX he
  have hNonzero : 0 < warpIndex l g := by omega
  obtain ⟨s, o, hIndex, hs, hr⟩ :=
    Prologue.nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero he hLate
  have hAt : At s 174 [(2535, b32 l.sharedBase)] :=
    hs.mono ⟨hs.2.2.2.2.2.1, trivial⟩
  obtain ⟨visits, hw⟩ := Mma.walkFromRun hr
  let route := CursorRoute.primingToSeed
  have hIn : route.inside s.pc = true := by rw [hs.1]; decide
  have hGet : ((X.tr g).drop 5)[index - 5]? = some e := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
  have hLow {v : Event} (h : route.inside v.pc = true) : v.pc < 909 :=
    (show 174 ≤ v.pc ∧ v.pc < 909 from of_decide_eq_true h).2
  rcases route.cutWalk hw hIn (ringShapeOfAt hAt) with hAll |
    ⟨t, before, tail, front, post, hSplit, _, hBefore, hStop, hShape, hKeep, hPrefix, hTail⟩
  · have hBad := hLow (eventInside route hw hAll e (List.mem_of_getElem? hGet))
    omega
  have hLowPrefix : ∀ event ∈ before, event.pc < 909 :=
    fun event hMem => hLow (eventInside route hPrefix hBefore event hMem)
  let start := 5 + before.length
  have hStart : start ≤ index := by
    by_contra! hEarly
    rw [hSplit, List.getElem?_append_left (by dsimp only [start] at hEarly; omega)] at hGet
    have := hLowPrefix e (List.mem_of_getElem? hGet)
    omega
  have hRemain : (X.tr g).drop start = tail := by
    dsimp only [start]
    rw [← List.drop_drop, hSplit, List.drop_append_length]
  have hSeen : tail[index - start]? = some e := by
    rw [← hRemain, List.getElem?_drop, Nat.add_sub_of_le hStart]
    exact he
  have hPc : t.pc = 909 := by
    simp only [route, CursorRoute.stops, List.mem_cons, List.not_mem_nil, or_false] at hStop
    rcases hStop with h | h | h
    · exact h
    all_goals
      have hBad := eventTailEvents loaderDrainFloor loaderDrainSegments hTail
        (show 1744 ≤ t.pc by omega) e (List.mem_of_getElem? hSeen)
      omega
  have hFacts : Holds t.regs [(2535, b32 l.sharedBase)] :=
    ⟨(hKeep _ (by decide)).trans hAt.2.2.2.2.1, trivial⟩
  have ht := pipelineAtCut hPc hShape hFacts
    (walkWithContinuingEventClean hTail (List.mem_of_getElem? hSeen) hContinues)
    ⟨_, Flow.code_909, rfl⟩
  obtain ⟨post, hWalk, hVisits⟩ := recurringWalkThroughEvent ht hTail hSeen hBand.2
  refine ⟨start, t, post, hStart, ?_, ht, hRemain.symm ▸ hWalk, fun v hv => (hVisits v hv).2⟩
  dsimp only [start]
  rw [List.take_add, hSplit, List.take_left]
  intro event hMem
  rcases List.mem_append.mp hMem with hEarly | hPriming
  · obtain ⟨j, hGet⟩ := List.mem_iff_getElem?.mp hEarly
    have hJ := (List.getElem?_eq_some_iff.mp hGet).1
    rw [List.length_take] at hJ
    have hBefore : j < 5 := by omega
    rw [List.getElem?_take_of_lt hBefore] at hGet
    by_contra! hFar
    obtain ⟨_, _, hOld, _, _⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero
      (show X.get (g, j) = some event from hGet) (by omega)
    omega
  · exact hLowPrefix event hPriming

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

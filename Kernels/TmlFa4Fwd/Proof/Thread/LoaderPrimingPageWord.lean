-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingScratchLoop
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCuQRead
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
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Loader

private theorem scratchExtra : PrimingScratchExtra [] := by
  refine ⟨⟨?_, by simp, ?_⟩, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem primingSuffix :
    (kernel.code.drop 515).all (fun ins => staysPastEvent 515 ins.op) = true := by decide +kernel

private theorem primingSegmentFloor :
    Assumptions.swExp2Sites.all (fun site => match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (515 ≤ seg.stop)
      | none => false) = true := by decide +kernel

private theorem noPageAfterScratch {X : Execution} {l : Launch} {g i j : Nat}
    {s : TState} {ending : Option TState} {a : Acc} {bytes : List (Option Byte)}
    (hPos : i ≤ j) (he : X.get (g, j) = some ⟨503, .rd a bytes⟩)
    (hS : s.pc = 515)
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop i) ending) : False := by
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRun
  have hMem : (⟨503, .rd a bytes⟩ : Event) ∈ (X.tr g).drop i := by
    apply List.mem_of_getElem? (i := j - i)
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  exact (by decide : ¬ 515 ≤ 503) (eventTailEventsOfSegmentFloor primingSuffix
    (fun site _ hm seg hs => by
      have h := List.all_eq_true.mp primingSegmentFloor site hm
      rw [hs] at h
      exact of_decide_eq_true h) hWalk hS.ge _ hMem)

private theorem afterDistinctHead {X : Execution} {g i j : Nat} {e f : Event}
    (hPos : i ≤ j) (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hNe : e ≠ f) : i + 1 ≤ j := by
  by_contra hn
  have eq : j = i := by omega
  rw [eq, he] at hf
  exact hNe (Option.some.inj hf)

private theorem primingScratchFindPage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j batch base : Nat} (hb : batch < p.batch) (entry : Fin 2)
    (hRow : base + 64 * entry.val < 2 ^ 31) (hFrame : OutputFootprint p X)
    {t : TState} (ht : At t 488 (primingScratchFacts p l batch base entry))
    {ending : Option TState} (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    {a : Acc} {bytes : List (Option Byte)} (hPos : i ≤ j)
    (he : X.get (g, j) = some ⟨503, .rd a bytes⟩) :
    (∃ row < p.kLength batch,
      a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}) ∨
    ∃ k ≤ j, ∃ u,
      At u (if entry.val == 0 then 488 else 515) (primingScratchFacts p l batch base 1) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop k) ending := by
  let row := base + 64 * entry.val
  obtain ⟨v, hv, hV⟩ := primingScratchPrepare hp hb entry hRow scratchExtra
    (by simpa only [List.append_nil] using ht)
  obtain ⟨w, hw, hW⟩ := primingScratchPageGuard (g := g) hV
  have hTail := hRun.after_local_nonempty (hv.trans (run_rtg hw)) (traceAfterObservedEvent he hPos)
  have hStore (k n : Nat) (u : TState) (hK : k ≤ j)
      (hAt : At u 504 ((7173, b32 n) :: (primingPageCarry p l batch row entry ++ [])))
      (hRest : Run kernel Assumptions.all l g u ((X.tr g).drop k) ending) :
      ∃ k' ≤ j, ∃ u',
        At u' (if entry.val == 0 then 488 else 515) (primingScratchFacts p l batch base 1) ∧
        Run kernel Assumptions.all l g u' ((X.tr g).drop k') ending := by
    obtain ⟨s, hs, hNext⟩ := primingPageStoreNext (g := g) hp entry scratchExtra.page hAt
    obtain ⟨_, _, hE, ⟨rfl, hU⟩, hRun'⟩ := hNext.continuing_at_nonempty (by
      rintro e ⟨_, hBad⟩; cases hBad) hRest (traceAfterObservedEvent he hK)
    obtain rfl := Option.some.inj hU
    have hK' := afterDistinctHead hK hE he (by intro h; cases congrArg Event.kind h)
    obtain ⟨s', hs', hNext'⟩ := primingScratchRowNext (g := g) hp hRow entry scratchExtra hs.next
    obtain ⟨_, _, hE', ⟨rfl, hU'⟩, hRun''⟩ := hNext'.continuing_at_nonempty (by
      rintro e ⟨_, hBad⟩; cases hBad) hRun' (traceAfterObservedEvent he hK')
    obtain rfl := Option.some.inj hU'
    have hK'' := afterDistinctHead hK' hE' he (by intro h; cases congrArg Event.kind h)
    obtain ⟨z, hz, hZ⟩ := primingScratchFinish (g := g) entry scratchExtra hs'.next
    exact ⟨_, hK'', z, by simpa only [List.append_nil] using hZ,
      hRun''.after_local_nonempty hz (traceAfterObservedEvent he hK'')⟩
  by_cases hLive : row < p.kLength batch
  · rw [ite_eq_left hLive] at hW
    obtain ⟨q, hNext, hQ, hAfter, hAt⟩ :=
      primingPageReadNext (g := g) hp hb hLive entry scratchExtra.page (hW.mono hW.2.2.2.2.2)
    obtain ⟨_, _, hRd, ⟨bs, _, rfl, hState⟩, hRest⟩ := hNext.continuing_at_nonempty (by
      rintro e ⟨_, _, _, hBad⟩; cases hBad) hTail (traceAfterObservedEvent he hPos)
    obtain rfl := Option.some.inj hState
    by_cases hEq : i = j
    · rw [hEq] at hRd
      exact .inl ⟨row, hLive,
        (Kind.rd.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hRd)))).1⟩
    have hMem : X.MemReads (.thread (g, i))
        {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4} bs := .inl ⟨q.pc, hRd⟩
    have hBytes := hX.launch_value (v := b32 (p.page batch (row / 16))) hMem rfl
      (primingPageProtected hp hb hLive (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame))
      (hp.pageBytes batch hb (row / 16) (by omega))
    rw [hBytes, hAfter] at hRest
    exact .inr (hStore (i + 1) _ _ (by omega) hAt hRest)
  · rw [ite_eq_right hLive] at hW
    exact .inr (hStore i 0 w hPos hW hTail)

/-- A loader observes a page lookup while initializing its two scratch rows. -/
@[no_expose] def LoaderPrimingPageRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨503, .rd a bytes⟩

/-- The guarded lookup addresses a live page of the selected request. -/
theorem LoaderPrimingPageRead.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)} (h : LoaderPrimingPageRead X i a bytes) :
    ∃ batch < p.batch, ∃ page < (p.kLength batch + 15) / 16,
      a = {loc := globalLoc (pageWordAddress p batch page), size := 4} := by
  obtain ⟨g, j⟩ := i
  have he : X.get (g, j) = some ⟨503, .rd a bytes⟩ := h
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < 503 by decide)
    (show 503 ∉ registerHintSites by decide)
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) 503 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hCuQ := hp.cuQ_protected (fun w a data loc => Thread.Loader.loaderOutputWrites hFrame
    (w := w) (a := a) (data := data) (loc := loc))
  have hWork := loaderOwnPrefixEventRequiresActiveTile hp hX hw hCuQ he
    (show 297 < 503 by decide) (show 503 < 1862 by decide)
  have hGet : X.get (warpLane l g lane, j) = some ⟨503, .rd a bytes⟩ := hLane.symm ▸ he
  obtain ⟨batch, hb, hLo, hHi, hTile, pos, hPos, t, ending, hAt, hRun, _⟩ :=
    loaderPrimingScratchOfActiveEvent hp hX hg hw hl
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hWork hGet (show 385 < 503 by decide)
  let tile := Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1
  let base := primingLaneRow tile (32 * warpIndex l g + lane)
  have hBase : base + 64 < 2 ^ 31 := by
    change 128 * tile + 127 < 2 ^ 31 at hTile
    simp only [base, primingLaneRow, kvCopyColumn, Bool.false_eq_true, ite_false, Nat.add_zero]
    omega
  have hScratch : At t 488 (primingScratchFacts p l batch base 0) := by
    exact hAt.mono ((holds_append ..).mp hAt.2.2.2.2).1
  have done (row : Nat) (hRow : row < p.kLength batch)
      (ha : a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}) :
      ∃ page < (p.kLength batch + 15) / 16,
        a = {loc := globalLoc (pageWordAddress p batch page), size := 4} :=
    ⟨row / 16, by omega, ha⟩
  refine ⟨batch, hb, ?_⟩
  rcases primingScratchFindPage hp hX hb 0 (by change base + 64 * 0 < _; omega)
    hFrame hScratch hRun hPos hGet with ⟨row, hr, ha⟩ | ⟨k, hk, u, hu, hR⟩
  · exact done row hr ha
  rcases primingScratchFindPage hp hX hb 1 (by exact hBase) hFrame hu hR hk hGet with
    ⟨row, hr, ha⟩ | ⟨n, hn, v, hv, hV⟩
  · exact done row hr ha
  · exact (noPageAfterScratch hn hGet hv.1 hV).elim

end PTX.Kernels.TmlFa4Fwd.Thread

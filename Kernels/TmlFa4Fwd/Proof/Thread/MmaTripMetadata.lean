-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaMaximalCacheExtent
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupShuffles
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRoute
public import Kernels.TmlFa4Fwd.Proof.MmaInitialPolls
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
import Kernels.TmlFa4Fwd.Proof.Termination
import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma
  (tripReadSite tripReadsWithEventsOfMaximal selectedTripPointer)

namespace MmaTripRead

/-- The three metadata observations of a selected MMA request. -/
@[no_expose] def Observed (X : Execution) (i : EvId) (which : Fin 3)
    (a : Acc) (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨(tripReadSite which).pc, .rd a bytes⟩

/-- The two CuQ endpoints and the used-K word of the selected request. -/
def access (p : Params) (batch : Nat) (which : Fin 3) : Acc :=
  if which = 2 then {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
  else {loc := globalLoc (p.cuQBase + 4 * (batch + which.val)), size := 4}

private theorem tripTailCode :
    (kernel.code.drop 2117).all (fun i => staysPastEvent 2117 i.op) = true := by decide +kernel

private theorem tripTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2117 ≤ seg.stop)
      | none => false) = true := by decide +kernel

private theorem accessOfMatchingRead {p : Params} {X : Execution} {i : EvId}
    {which expected : Fin 3} {batch : Nat} {a : Acc} {bytes vals : List (Option Byte)}
    (hRead : Observed X i which a bytes)
    (hKnown : Observed X i expected (access p batch expected) vals) :
    a = access p batch which := by
  have hEvent := Option.some.inj (hRead.symm.trans hKnown)
  have hSite := congrArg Event.pc hEvent
  have hUnique : ∀ which expected : Fin 3, (tripReadSite which).pc = (tripReadSite expected).pc →
      which = expected := by decide
  obtain rfl := hUnique _ _ hSite
  exact (Kind.rd.inj (congrArg Event.kind hEvent)).1

/-- An observed MMA trip read in any consistent prefix addresses a bounded launch
word. A maximal extension recovers the selected request without altering the read. -/
theorem Observed.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrames : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {i : EvId} {which : Fin 3} {a : Acc} {bytes : List (Option Byte)}
    (hr : Observed X i which a bytes) : ∃ batch < p.batch, a = access p batch which := by
  obtain ⟨g,j⟩ := i
  let e : Event := ⟨(tripReadSite which).pc, .rd a bytes⟩
  have he : X.get (g,j) = some e := hr
  have hg := event_thread_lt hX he
  have hSites : ∀ i : Fin 3, 2110 ≤ (tripReadSite i).pc ∧ (tripReadSite i).pc < 2117 ∧
      (tripReadSite i).pc ∉ registerHintSites := by decide
  have hAfterStartup := (show 173 < 2110 by decide).trans_le (hSites which).1
  have hRole := roleBodyPcOfEvent hp hX he hAfterStartup (hSites which).2.2
  have hw : warpIndex l g = 12 := by
    change roleBodyPc (warpIndex l g) (tripReadSite which).pc at hRole
    have hLo := (hSites which).1
    have hHi := (hSites which).2.1
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨Y,hY,hPrefix,hLargest⟩ := bounded_largest_extension (terminates hp) hX
  have hMax : Maximal l kernel Assumptions.all m Y :=
    ⟨hY, fun Z hZ hExt => hLargest Z hZ (Execution.le_trans hPrefix hExt)⟩
  have hRead := Execution.le_get hPrefix he
  obtain ⟨hCuQ,hUsedK⟩ := (hFrames Y hY).metadataProtected hp
  have hActive : g / l.block < tilePrefix p p.batch * p.heads := by
    by_contra! hIdle
    exact TmlFa4Fwd.Mma.idleMmaNoTileWorkEvent hp hMax hg hw hCuQ hIdle hRead
      ((show 2042 ≤ 2110 by decide).trans (hSites which).1)
      ((hSites which).2.1.trans (show 2117 < 2763 by decide))
  obtain ⟨batch, ⟨hb,hLo,hHi⟩, _⟩ := tileBatch_existsUnique p hActive
  obtain ⟨pos,_,u,_,hPos,hBound,_,_,hRelease,hAt,hPast,hLocal,hRun⟩ :=
    Allocation.mmaMetadataOfMaximal hp hMax hg hw hCuQ hb hLo hHi
  have hReached := Thread.Mma.selectedMetadataBeforeBodyEvent hPast hLocal hAt.1
    hRead (hSites which).1
  obtain ⟨_,hPtr,hEntry⟩ := selectedTripPointer hp g hb u hAt
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨_,hq₀,hq₁,hk,hv,_,hTail,_,_⟩ :=
    tripReadsWithEventsOfMaximal hp hMax hg hb (by omega) hEntry
      (fun lane hLane => hCuQ (batch+lane) (by omega)) (hUsedK batch hb)
      hPast hRun (hLocal.trans (run_rtg hPtr)) hPos hBound hRelease
  have hEarly : j < pos + 3 := by
    by_contra! hAfter
    have hi : ((Y.tr g).drop (pos+3))[j-(pos+3)]? = some e := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hAfter]
      exact hRead
    obtain ⟨_,hWalk⟩ := TmlFa4Fwd.Mma.walkFromRun hTail
    have hLate := eventTailEvents tripTailCode tripTailSegments hWalk hv.1.ge e
      (List.mem_of_getElem? hi)
    exact Nat.not_le_of_lt (hSites which).2.1 hLate
  refine ⟨batch,hb,?_⟩
  have hOffset : j = pos ∨ j = pos+1 ∨ j = pos+2 := by omega
  have hObserved : Observed Y (g,j) which a bytes := hRead
  rcases hOffset with rfl | rfl | rfl
  · exact accessOfMatchingRead (expected := 0) hObserved hq₀
  · exact accessOfMatchingRead (expected := 1) hObserved hq₁
  · exact accessOfMatchingRead (expected := 2) hObserved hk

end MmaTripRead
end PTX.Kernels.TmlFa4Fwd.Thread

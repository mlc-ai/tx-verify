-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates
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

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The loader's read of the selected request's used-K length. -/
@[no_expose] def LoaderUsedKRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨385, .rd a bytes⟩

theorem LoaderUsedKRead.reads {X : Execution} {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (h : LoaderUsedKRead X i a bytes) : X.Reads i a bytes :=
  ⟨385, h⟩

set_option maxRecDepth 100000 in
private theorem usedKReadSuffix :
    (kernel.code.drop 386).all (fun ins => staysPastEvent 386 ins.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem usedKReadSegments :
    Assumptions.swExp2Sites.all (fun site => match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (386 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

/-- The actual loader metadata read accesses an in-bounds request word and returns its
launch value. An observed read supplies the required prefix even without a later event. -/
theorem LoaderUsedKRead.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (h : LoaderUsedKRead X i a bytes) :
    ∃ batch < p.batch, a = {loc := globalLoc (p.usedKBase + 4 * batch), size := 4} ∧
      bytes = (b32 (p.kLength batch)).toBytes.map some := by
  obtain ⟨g, j⟩ := i
  have he : X.get (g, j) = some ⟨385, .rd a bytes⟩ := h
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < 385 by decide)
    (show 385 ∉ registerHintSites by decide)
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) 385 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have writes := fun w a data loc => Loader.loaderOutputWrites hFrame (w := w) (a := a)
    (data := data) (loc := loc)
  have hCuQ := hp.cuQ_protected writes
  have hWork := loaderOwnPrefixEventRequiresActiveTile hp hX hw hCuQ he
    (show 297 < 385 by decide) (show 385 < 1862 by decide)
  obtain ⟨batch, hb, _, _, ends, cur, hFollow⟩ := loaderPrimingEntryOfActiveEvent
    hp hX hg hw hl hCuQ hWork (hLane.symm ▸ he) (show 308 < 385 by decide)
  have hExtra : ActiveReadExtra (primingKActiveAbi p l (warpIndex l g)) := by
    constructor
    · simp [primingKActiveAbi, addressCacheInputs]
    · simp [primingKActiveAbi, addressCacheInputs]
    · simp [primingKActiveAbi, addressCacheInputs]
    · set_option maxRecDepth 100000 in kernel_rfl
  have hDemand : PrefixDemand X (warpLane l g lane) (cur.pos lane) 384 (ends lane) :=
    .inr ⟨j, ⟨385, .rd a bytes⟩, hFollow.before, (show 384 < 385 by decide), hFollow.get⟩
  obtain ⟨u, h0, h1, h2, hAt, hTail⟩ := loaderActiveReadWordsFrameInPrefix
    hp hX writes hb hExtra (cur.checkpoint lane hl)
    ((cur.continuation lane hl).after_local_nonempty (cur.localSteps lane hl) hFollow.nonempty)
    hDemand
  have hPosition : j = cur.pos lane + 1 + 1 := by
    have hBefore := hFollow.before
    rcases Nat.lt_trichotomy j (cur.pos lane + 1 + 1) with hEarly | hEq | hLate
    · have hDiff {q : Nat} {e : Event} (hSite : e.pc < 385)
          (hGet : X.get (warpLane l g lane, q) = some e) : j ≠ q := by
        rintro rfl
        have hEq := congrArg Event.pc (Option.some.inj (hGet.symm.trans hFollow.get))
        change e.pc = 385 at hEq
        omega
      have h0Ne := hDiff (show 381 < 385 by decide) h0
      have h1Ne := hDiff (show 382 < 385 by decide) h1
      omega
    · exact hEq
    · obtain ⟨_, hWalk⟩ := Mma.walkFromRun hTail
      have hMem : (⟨385, .rd a bytes⟩ : Event) ∈
          (X.tr (warpLane l g lane)).drop (cur.pos lane + 1 + 1 + 1) := by
        apply List.mem_of_getElem? (i := j - (cur.pos lane + 1 + 1 + 1))
        rw [List.getElem?_drop, Nat.add_sub_of_le (show cur.pos lane + 1 + 1 + 1 ≤ j by omega)]
        exact hFollow.get
      have hFloor := eventTailEvents usedKReadSuffix usedKReadSegments hWalk
        (show 386 ≤ u.pc by rw [hAt.1]) _ hMem
      exact ((show ¬ 386 ≤ 385 by decide) hFloor).elim
  have hRead := hFollow.get
  rw [hPosition] at hRead
  have hKind := congrArg Event.kind (Option.some.inj (hRead.symm.trans h2))
  cases hKind
  exact ⟨batch, hb, rfl, rfl⟩

end PTX.Kernels.TmlFa4Fwd.Thread

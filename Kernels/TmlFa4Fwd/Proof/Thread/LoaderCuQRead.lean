-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderUsedKRead
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

/-- The active loader observes one of the selected request's two cumulative-query words. -/
@[no_expose] def LoaderCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  ∃ site, (site = 381 ∨ site = 382) ∧ X.get i = some ⟨site, .rd a bytes⟩

private theorem cuQSuffix (site : Nat) (hSite : site = 381 ∨ site = 382) :
    (kernel.code.drop (site + 1)).all (fun ins => staysPastEvent (site + 1) ins.op) = true := by
  rcases hSite with rfl | rfl <;> decide +kernel

private theorem cuQSegments :
    Assumptions.swExp2Sites.all (fun site => match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (383 ≤ seg.stop)
      | none => false) = true := by
  decide +kernel

private theorem observedLoaderCuQRead {X : Execution} {l : Launch} {g pos j site : Nat}
    {t : TState} {ending : Option TState} {a b : Acc} {bytes data : List (Option Byte)}
    (hSite : site = 381 ∨ site = 382) (hPos : pos ≤ j)
    (he : X.get (g, j) = some ⟨site, .rd a bytes⟩)
    (hRead : X.get (g, pos) = some ⟨site, .rd b data⟩) (ht : t.pc = site + 1)
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop (pos + 1)) ending) :
    a = b ∧ bytes = data := by
  apply metadataReadPayloadOfSuffix hPos he hRead
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hTail
  exact eventTailEventsOfSegmentFloor (cuQSuffix site hSite)
    (fun q _ hm seg hs => by
      have h := List.all_eq_true.mp cuQSegments q hm
      rw [hs] at h
      have hEnd : 383 ≤ seg.stop := of_decide_eq_true h
      omega) hWalk ht.ge

/-- Both actually observed loader CuQ words have launch backing and launch bytes. -/
theorem LoaderCuQRead.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (h : LoaderCuQRead X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} ∧
      bytes = (b32 (p.qOffset index)).toBytes.map some := by
  obtain ⟨g, j⟩ := i
  obtain ⟨site, hSite, he⟩ := h
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < site by omega) (by
    change site ∉ registerHintSites
    rcases hSite with rfl | rfl <;> decide)
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) site at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hCuQ := hp.cuQ_protected (fun w a data loc => Loader.loaderOutputWrites hFrame
    (w := w) (a := a) (data := data) (loc := loc))
  have hWork := loaderOwnPrefixEventRequiresActiveTile hp hX hw hCuQ he
    (show 297 < site by omega) (show site < 1862 by omega)
  obtain ⟨batch, hb, _, _, ending, cur, hFollow⟩ := loaderPrimingEntryOfActiveEvent
    hp hX hg hw hl hCuQ hWork (hLane.symm ▸ he) (show 308 < site by omega)
  let base := p.cuQBase + 4 * batch
  let pos := cur.pos lane
  have hAt : At (cur.state lane) 381 [(7515, b64 base)] :=
    (cur.checkpoint lane hl).mono ⟨(cur.checkpoint lane hl).2.2.2.2.1, trivial⟩
  have hRun := (cur.continuation lane hl).after_local_nonempty
    (cur.localSteps lane hl) hFollow.nonempty
  rw [hLane] at hRun
  have hStart : pos ≤ j := hFollow.before
  have hMore {n : Nat} (hBefore : n ≤ j) : (X.tr g).drop n ≠ [] := by
    intro hn
    exact Nat.not_le_of_lt (len_of_get he) ((List.drop_eq_nil_iff.mp hn).trans hBefore)
  obtain ⟨_, hFirst, hv, hTail⟩ := activeFirstCuQRead hp hX hb hAt hAt.2.2.2.2.1
    (hCuQ batch hb.le) (by simp) hRun (hMore hStart)
  rcases hSite with rfl | rfl
  · exact ⟨batch, hb.le, observedLoaderCuQRead (.inl rfl) hStart he hFirst hv.1 hTail⟩
  · have hNext : pos + 1 ≤ j := by
      by_contra hNot
      have hEq : j = pos := by omega
      rw [hEq] at he
      have hPc := congrArg Event.pc (Option.some.inj (he.symm.trans hFirst))
      exact (by decide : (382 : Nat) ≠ 381) hPc
    obtain ⟨_, hSecond, hu, hRest⟩ := activeSecondCuQRead hp hX hb hv hv.2.2.2.2.2.1
      (hCuQ (batch + 1) (by omega)) (by simp) hTail (hMore hNext)
    exact ⟨batch + 1, by omega, observedLoaderCuQRead (.inr rfl) hNext he hSecond hu.1 hRest⟩

end PTX.Kernels.TmlFa4Fwd.Thread

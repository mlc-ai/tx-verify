-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
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
open PTX.Kernels.TmlFa4Fwd.Correction

/-- The correction lane reads the selected request's used-K length. -/
@[no_expose] def CorrectionUsedKRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨7959, .rd a bytes⟩

private theorem usedKReadSuffix :
    (kernel.code.drop 7960).all (fun ins => staysPastEvent 7960 ins.op) = true := by
  decide +kernel

private theorem correctionMetadataEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g j site : Nat} {a : Acc}
    {bytes : List (Option Byte)}
    (hSite : site = 7955 ∨ site = 7956 ∨ site = 7959)
    (he : X.get (g, j) = some ⟨site, .rd a bytes⟩) :
    ∃ batch < p.batch, ∃ (pos : Nat) (t : TState) (ending : Option TState),
      At t 7955 (correctionInputFacts p batch (assignedCoordinates p batch (g / l.block)).1 ++ []) ∧
      pos ≤ j ∧ Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending := by
  have hg : g < l.threads := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < site by omega)
    (by
      change site ∉ registerHintSites
      obtain rfl | rfl | rfl := hSite <;> decide)
  have hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    change roleBodyPc (warpIndex l g) site at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hGet : X.get (warpLane l g lane, j) = some ⟨site, .rd a bytes⟩ := hLane.symm ▸ he
  have hWork := correctionWorkOfLateEvent hp hX hg hw.1 hw.2 hl
    (show 7859 < site by omega) (show site < 9201 by omega) hGet
  obtain ⟨batch, hb, _, _, ending, _, _, active, hFollow⟩ :=
    correctionActiveTileOfEvent hp hX hg hw.1 hw.2 hl hWork
      (show 7884 < site by omega) hGet
  obtain ⟨t, hRun, hAt⟩ := correctionInputRun hp hb (active.checkpoint lane hl)
  have hInput : At t 7955
      (correctionInputFacts p batch (assignedCoordinates p batch (g / l.block)).1 ++ []) :=
    hAt.mono (by
      rw [List.append_nil]
      exact ((holds_append _ _ _).mp ((holds_append _ _ _).mp hAt.2.2.2.2).1).1)
  have hSuffix := (active.continuation lane hl).after_local_nonempty
    ((active.localSteps lane hl).trans (run_rtg hRun)) hFollow.nonempty
  rw [hLane] at hSuffix
  exact ⟨batch, hb, active.pos lane, t, ending lane, hInput, hFollow.before, hSuffix⟩

private theorem nonemptyAtObserved {X : Execution} {g pos j : Nat} {e : Event}
    (hBefore : pos ≤ j) (hGet : X.get (g, j) = some e) : (X.tr g).drop pos ≠ [] := by
  intro hEmpty
  exact Nat.not_le_of_lt (len_of_get hGet) ((List.drop_eq_nil_iff.mp hEmpty).trans hBefore)

/-- The actual read has the bounded request address and the protected launch value,
including when it is the last event of a consistent prefix. -/
theorem CorrectionUsedKRead.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    {i : EvId} {a : Acc} {bytes : List (Option Byte)} (h : CorrectionUsedKRead X i a bytes) :
    ∃ batch < p.batch, a = {loc := globalLoc (p.usedKBase + 4 * batch), size := 4} ∧
      bytes = (b32 (p.kLength batch)).toBytes.map some := by
  obtain ⟨g, j⟩ := i
  have he : X.get (g, j) = some ⟨7959, .rd a bytes⟩ := h
  obtain ⟨batch, hb, pos, t, ending, hInput, hStart, hRun⟩ :=
    correctionMetadataEntry hp hX (.inr (.inr rfl)) he
  obtain ⟨u, hu, hTail, h0, h1, _, _⟩ :=
    correctionCuQReadsToUsedKInPrefix (first := 7959) hp hX hb hInput
      (by simp) (by decide +kernel)
      hRun (.inr ⟨j, ⟨7959, .rd a bytes⟩, hStart, Nat.le_refl _, he⟩) (by decide)
  have hBefore : pos + 2 ≤ j := by
    by_contra hNot
    rcases (show j = pos ∨ j = pos + 1 by omega) with eq | eq
    · rw [eq] at he
      have eq := congrArg Event.pc (Option.some.inj (he.symm.trans h0))
      exact (by decide : (7959 : Nat) ≠ 7955) eq
    · rw [eq] at he
      have eq := congrArg Event.pc (Option.some.inj (he.symm.trans h1))
      exact (by decide : (7959 : Nat) ≠ 7956) eq
  rw [List.append_nil] at hu
  obtain ⟨observed, v, hPc, hRest⟩ :=
    correctionUsedKLoadInPrefix hp hX hb hu (hUsedK batch hb) hTail (nonemptyAtObserved hBefore he)
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRest
  refine ⟨batch, hb, metadataReadPayloadOfSuffix hBefore he observed ?_⟩
  exact eventTailEventsOfSegmentFloor usedKReadSuffix
    (fun site _ hSite _ _ => by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
      omega) hWalk hPc.ge

/-- The correction lane reads one of the selected request's two cumulative-query words. -/
@[no_expose] def CorrectionCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  ∃ site, (site = 7955 ∨ site = 7956) ∧ X.get i = some ⟨site, .rd a bytes⟩

private theorem correctionCuQReadSuffix (site : Nat) (hSite : site = 7955 ∨ site = 7956) :
    (kernel.code.drop (site + 1)).all (fun ins => staysPastEvent (site + 1) ins.op) = true := by
  rcases hSite with rfl | rfl <;> decide +kernel

private theorem observedCorrectionCuQRead {X : Execution} {l : Launch} {g pos j site : Nat}
    {t : TState} {ending : Option TState} {a b : Acc} {bytes data : List (Option Byte)}
    (hSite : site = 7955 ∨ site = 7956) (hPos : pos ≤ j)
    (he : X.get (g, j) = some ⟨site, .rd a bytes⟩)
    (hRead : X.get (g, pos) = some ⟨site, .rd b data⟩) (ht : t.pc = site + 1)
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop (pos + 1)) ending) :
    a = b ∧ bytes = data := by
  apply metadataReadPayloadOfSuffix hPos he hRead
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hTail
  exact eventTailEventsOfSegmentFloor (correctionCuQReadSuffix site hSite)
    (fun q hq hm _ _ => by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hm
      omega) hWalk ht.ge

/-- Both actually observed correction CuQ words have launch backing and launch bytes. -/
theorem CorrectionCuQRead.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (h : CorrectionCuQRead X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} ∧
      bytes = (b32 (p.qOffset index)).toBytes.map some := by
  obtain ⟨g, j⟩ := i
  obtain ⟨site, hSite, he⟩ := h
  obtain ⟨batch, hb, pos, t, ending, hInput, hStart, hRun⟩ :=
    correctionMetadataEntry hp hX (hSite.elim Or.inl (Or.inr ∘ Or.inl)) he
  obtain ⟨hFirst, hAt, hTail, _⟩ := correctionFirstCuQInPrefix hp hX hb hInput (by simp)
    hRun (nonemptyAtObserved hStart he)
  rcases hSite with rfl | rfl
  · exact ⟨batch, hb.le, observedCorrectionCuQRead (.inl rfl) hStart he hFirst hAt.1 hTail⟩
  · have hNext : pos + 1 ≤ j := by
      by_contra hNot
      have hEq : j = pos := by omega
      rw [hEq] at he
      have hPc := congrArg Event.pc (Option.some.inj (he.symm.trans hFirst))
      exact (by decide : (7956 : Nat) ≠ 7955) hPc
    obtain ⟨hSecond, hu, hRest, _⟩ := correctionSecondCuQInPrefix hp hX hb hAt (by simp)
      hTail (nonemptyAtObserved hNext he)
    exact ⟨batch + 1, by omega,
      observedCorrectionCuQRead (.inr rfl) hNext he hSecond hu.1 hRest⟩

end PTX.Kernels.TmlFa4Fwd.Thread

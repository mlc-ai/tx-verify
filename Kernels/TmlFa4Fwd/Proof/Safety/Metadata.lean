-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.GlobalConflicts
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionMetadataReads
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFallbackWord
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxFallbackWord
public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryScoreCommitOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.EpilogueLaterDrainCuQRead
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainAddressClass
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.EpilogueComplete
public import Kernels.TmlFa4Fwd.Proof.Termination
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFallbackWord
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLaterDrainWord
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaGroupedCuQWords
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialCuQReads
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCuQRead
public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataCuQClasses
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.OutputReadFacts
import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Thread Epilogue Allocation

/-- A launch metadata word and its value, with the semantic bounds for its array. -/
inductive MetadataWord (p : Params) : MetadataKind → Acc → Nat → Prop where
  | cuQ (index : Nat) (inBounds : index ≤ p.batch) :
      MetadataWord p .cuQ
        {loc := globalLoc (p.cuQBase + 4 * index), size := 4} (p.qOffset index)
  | usedK (batch : Nat) (inBounds : batch < p.batch) :
      MetadataWord p .usedK
        {loc := globalLoc (p.usedKBase + 4 * batch), size := 4} (p.kLength batch)
  | pageTable (batch page : Nat) (batchInBounds : batch < p.batch)
      (pageInBounds : page < (p.kLength batch + 15) / 16) :
      MetadataWord p .pageTable
        {loc := globalLoc (p.pageTableBase + 4 * (batch * p.pageTableStride + page)), size := 4}
        (p.page batch page)

/-- All four bytes of a bounded metadata word have launch backing. -/
theorem MetadataWord.backed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {kind : MetadataKind} {a : Acc} {value : Nat} (hWord : MetadataWord p kind a value) :
    a.size = 4 ∧ HasValue m a.loc (.bits 32 (BitVec.ofNat 64 value)) := by
  cases hWord with
  | cuQ b hb => exact ⟨rfl, hp.cuQ b hb⟩
  | usedK b hb => exact ⟨rfl, hp.usedK b hb⟩
  | pageTable b page hb hPage => exact ⟨rfl, hp.pageBytes b hb page hPage⟩

/-- Every address covered by a bounded metadata read is allocated at launch. -/
theorem MetadataWord.allocated {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {kind : MetadataKind} {a : Acc} {value : Nat} (hWord : MetadataWord p kind a value)
    {loc : Loc} (hCover : a.Covers loc) : ∃ byte, m loc = some (some byte) := by
  obtain ⟨hSize, hValue⟩ := hWord.backed hp
  obtain ⟨hSpace, hCta, hLo, hHi⟩ := hCover
  let k := loc.addr - a.loc.addr
  have hk : k < 4 := by dsimp [k]; omega
  have hLoc : a.loc.at k = loc := by
    obtain ⟨sp, cta, addr⟩ := loc
    simp only [Loc.at, Loc.mk.injEq, hSpace.symm, hCta.symm, true_and]
    exact Nat.add_sub_of_le (show a.loc.addr ≤ addr from hLo)
  exact ⟨_, hLoc ▸ hValue k hk⟩

/-- A covering metadata byte belongs to the array's launch input region. -/
theorem MetadataWord.inInput {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {kind : MetadataKind} {a : Acc} {value : Nat} (hWord : MetadataWord p kind a value)
    {loc : Loc} (hCovers : a.Covers loc) :
    ∃ region ∈ p.inputRegions, region.Contains loc := by
  obtain ⟨hSpace, hCta, hLo, hHi⟩ := hCovers
  cases hWord with
  | cuQ b hb =>
    refine ⟨⟨p.cuQBase, 4 * (p.batch + 1)⟩, by simp [Params.inputRegions],
      hSpace, hCta, ?_, ?_⟩ <;>
      dsimp only [globalLoc] at hLo hHi ⊢ <;> omega
  | usedK b hb =>
    refine ⟨⟨p.usedKBase, 4 * p.batch⟩, by simp [Params.inputRegions],
      hSpace, hCta, ?_, ?_⟩ <;>
      dsimp only [globalLoc] at hLo hHi ⊢ <;> omega
  | pageTable b page hb hPage =>
    have hStride : page < p.pageTableStride :=
      hPage.trans_le (hp.pageTable b hb).1
    have hRow : (b + 1) * p.pageTableStride ≤ p.batch * p.pageTableStride :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hRow
    refine ⟨⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩, by simp [Params.inputRegions],
      hSpace, hCta, ?_, ?_⟩
    · dsimp only [globalLoc] at hLo ⊢
      omega
    · rw [Nat.mul_assoc]
      dsimp only [globalLoc] at hHi ⊢
      omega

/-- Every role starts its scheduler by reading the same bounded launch word in that lane. -/
theorem initialCuQWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)} (hRead : InitialCuQRead X i a bytes) :
    MetadataWord p .cuQ a (p.qOffset (laneOf l i.1)) := by
  obtain ⟨hLane, rfl⟩ := hRead.footprint hp hX
  exact .cuQ _ hLane

/-- Address bounds from replaying repeated scheduler and drain lookups. -/
structure CuQReplayAddresses (p : Params) (X : Execution) : Prop where
  outputFallback : OutputFallbackAddresses p X
  loaderFallback : LoaderFallbackAddresses p X
  laterDrain : OutputLaterDrainAddresses p X
  softmaxFallback : SoftmaxFallbackAddresses p X
  correctionFallback : CorrectionFallbackAddresses p X

/-- A metadata observation whose address is not covered by a launch word. -/
structure UnbackedMetadataRead (p : Params) (X : Execution) (i : EvId)
    (a : Acc) (bytes : List (Option Byte)) : Prop where
  metadata : MetadataRead X i .cuQ a bytes
  size : a.size = 4
  unbacked : ¬ ∃ kind value, MetadataWord p kind a value
  notInitialCuQ : ¬ InitialCuQRead X i a bytes
  notLoaderCuQ : ¬ LoaderCuQRead X i a bytes
  notCorrectionCuQ : ¬ CorrectionCuQRead X i a bytes
  notOutputCuQ : ¬ OutputCuQRead X i a bytes
  notOutputDrainCuQ : ¬ OutputDrainCuQRead X i a bytes
  notOutputLaterDrainCuQ : ¬ OutputLaterDrainCuQRead X i a bytes
  notOutputFallbackCuQ : ¬ OutputFallbackCuQRead X i a bytes
  notLoaderFallbackCuQ : ¬ LoaderFallbackCuQRead X i a bytes
  notLoaderFirstDrainCuQ : ¬ Thread.Loader.FirstDrainCuQRead X i a bytes
  notLoaderLaterDrainCuQ : ¬ Thread.Loader.LaterDrainCuQRead X i a bytes
  notMmaInitialDrainCuQ : ¬ MmaInitialDrainCuQRead X i a bytes
  notMmaGroupedCuQ : ∀ group, ¬ MmaGroupedCuQRead group X i a bytes
  notMmaTrip : ∀ which, ¬ MmaTripRead.Observed X i which a bytes
  notSoftmaxFallbackCuQ : ¬ SoftmaxFallbackCuQRead X i a bytes
  notCorrectionFallbackCuQ : ¬ CorrectionFallbackCuQRead X i a bytes
  notSoftmaxGeometry : ∀ which, ¬ SoftmaxGeometryRead X i which a bytes

/-- Initial scheduler reads and the classified trip-count inputs have bounded
launch words even in a prefix ending at the read. -/
theorem unbackedMetadataRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrames : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hAddresses : CuQReplayAddresses p X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (hRead : X.Reads i a bytes) (hGlobal : a.loc.space = .global)
    (hMissing : ¬ ∃ kind value, MetadataWord p kind a value) :
    UnbackedMetadataRead p X i a bytes := by
  obtain ⟨hMetadata, hSize⟩ := globalMetadataRead hX hRead hGlobal
  have hFrame := hFrames X hX
  obtain ⟨hCuQ, hUsedK⟩ := hFrame.metadataProtected hp
  have hClass : MetadataRead X i .cuQ a bytes := by
    obtain ⟨kind, hKind⟩ := hMetadata
    cases kind with
    | cuQ => exact hKind
    | usedK =>
      exfalso
      rcases hKind.usedK with hLoader | hMma | hSoftmax | hCorrection
      · obtain ⟨batch, hb, rfl, _⟩ := hLoader.word hp hX hFrame
        exact hMissing ⟨_, _, .usedK batch hb⟩
      · obtain ⟨batch, hb, rfl⟩ := hMma.word hp hX hFrames
        exact hMissing ⟨_, _, .usedK batch hb⟩
      · obtain ⟨batch, hb, _, _, rfl, _⟩ := hSoftmax.word hp hX hFrame
        exact hMissing ⟨_, _, .usedK batch hb⟩
      · obtain ⟨batch, hb, rfl, _⟩ := hCorrection.word hp hX hUsedK
        exact hMissing ⟨_, _, .usedK batch hb⟩
    | pageTable =>
      exfalso
      rcases hKind.pageTable with hPriming | hRecurring
      · obtain ⟨batch, hb, page, hPageBound, rfl⟩ := hPriming.word hp hX hFrame
        exact hMissing ⟨_, _, .pageTable batch page hb hPageBound⟩
      · obtain ⟨batch, hb, page, hPageBound, rfl⟩ := hRecurring.word hp hX hFrame
        exact hMissing ⟨_, _, .pageTable batch page hb hPageBound⟩
  have hDrainProtected : ∀ Y, Consistent l kernel Assumptions.all m Y → DrainCuQProtected p Y :=
    fun Y hY => ((hFrames Y hY).metadataProtected hp).1
  refine ⟨hClass, hSize, hMissing, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hInitial => hMissing ⟨_, _, initialCuQWord hp hX hInitial⟩
  · intro hReadCuQ
    obtain ⟨index, hi, rfl, _⟩ := hReadCuQ.word hp hX hFrame
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hReadCuQ
    obtain ⟨index, hi, rfl, _⟩ := hReadCuQ.word hp hX
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hOutput
    obtain ⟨index, hi, rfl⟩ := OutputWarp.cuQReadWord hp hX hOutput
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hDrain
    obtain ⟨index, hi, rfl⟩ := OutputWarp.drainCuQReadWord hp hX hDrain
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hReadDrain
    obtain ⟨index, hi, rfl⟩ := hAddresses.laterDrain i a bytes hReadDrain
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hReadFallback
    obtain ⟨index, hi, rfl⟩ := hAddresses.outputFallback i a bytes hReadFallback
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hReadFallback
    obtain ⟨index, hi, rfl⟩ := hAddresses.loaderFallback i a bytes hReadFallback
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hFirstDrain
    obtain ⟨index, hi, rfl⟩ := hFirstDrain.word hp hX hCuQ
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hLaterDrain
    obtain ⟨index, hi, rfl⟩ := hLaterDrain.word hp hX hCuQ
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hMmaDrain
    obtain ⟨index, hi, rfl⟩ :=
      mmaInitialDrainAddressesOfMaximal hp hX hDrainProtected i a bytes hMmaDrain
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro group hMmaLookup
    obtain ⟨index, hi, rfl⟩ :=
      mmaGroupedCuQAddressesOfMaximal hp hX hDrainProtected group i a bytes hMmaLookup
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro which hTrip
    obtain ⟨batch, hb, rfl⟩ := hTrip.word hp hX hFrames
    apply hMissing
    fin_cases which
    · exact ⟨_, _, .cuQ batch hb.le⟩
    · exact ⟨_, _, .cuQ (batch + 1) (by omega)⟩
    · exact ⟨_, _, .usedK batch hb⟩
  · intro hReadFallback
    obtain ⟨index, hi, rfl⟩ := hAddresses.softmaxFallback i a bytes hReadFallback
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro hReadFallback
    obtain ⟨index, hi, rfl⟩ := hAddresses.correctionFallback i a bytes hReadFallback
    exact hMissing ⟨_, _, .cuQ index hi⟩
  · intro which hReadGeom
    obtain ⟨batch,hb,_,_,rfl,_⟩ := hReadGeom.word hp hX hFrame
    apply hMissing
    fin_cases which
    · exact ⟨_,_,.cuQ batch hb.le⟩
    · exact ⟨_,_,.cuQ (batch+1) (by omega)⟩
    · exact ⟨_,_,.usedK batch hb⟩

/-- Every decoded CuQ lookup excluded by the safety classifier is either replayed
in that classifier or a bounded read in one of the row drains. -/
theorem UnbackedMetadataRead.impossible {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (hBad : UnbackedMetadataRead p X i a bytes) : False := by
  cases hBad.metadata.cuQ with
  | initial h => exact hBad.notInitialCuQ h
  | loaderGeometry h => exact hBad.notLoaderCuQ h
  | loaderFallback h => exact hBad.notLoaderFallbackCuQ h
  | loaderFirstDrain h => exact hBad.notLoaderFirstDrainCuQ h
  | loaderLaterDrain h => exact hBad.notLoaderLaterDrainCuQ h
  | mmaTrip which h => exact hBad.notMmaTrip which h
  | mmaFirstDrain h => exact hBad.notMmaInitialDrainCuQ h
  | mmaGrouped group h => exact hBad.notMmaGroupedCuQ group h
  | outputGeometry h => exact hBad.notOutputCuQ h
  | outputFallback h => exact hBad.notOutputFallbackCuQ h
  | outputFirstDrain h => exact hBad.notOutputDrainCuQ h
  | outputLaterDrain h => exact hBad.notOutputLaterDrainCuQ h
  | softmaxGeometry which h => exact hBad.notSoftmaxGeometry which h
  | softmaxFallback h => exact hBad.notSoftmaxFallbackCuQ h
  | correctionGeometry h => exact hBad.notCorrectionCuQ h
  | correctionFallback h => exact hBad.notCorrectionFallbackCuQ h
  | rowFirstDrain _ h =>
    obtain ⟨index, hIndex, rfl⟩ := h.word hp hX (hFrame.metadataProtected hp).1
    exact hBad.unbacked ⟨_, _, .cuQ index hIndex⟩
  | rowLaterDrain _ h =>
    obtain ⟨index, hIndex, rfl⟩ := h.word hp hX (hFrame.metadataProtected hp).1
    exact hBad.unbacked ⟨_, _, .cuQ index hIndex⟩

end PTX.Kernels.TmlFa4Fwd.Safety

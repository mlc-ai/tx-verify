-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReadClasses
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialCuQReads
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCuQRead
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLaterDrainWord
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaGroupedCuQWords
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
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
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainAddressClass
public import Kernels.TmlFa4Fwd.Proof.EpilogueComplete
public import Kernels.TmlFa4Fwd.Proof.Termination
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxFallbackWord
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFallbackWord
public import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainLaterWords
import all Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import all Kernels.TmlFa4Fwd.Proof.Thread.InitialCuQReads
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderFallbackWord
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderCuQRead
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderLaterDrainWord
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTripMetadata
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputCuQReadClass
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Assumptions
import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
import Kernels.TmlFa4Fwd.Proof.NoCancellation
import Kernels.TmlFa4Fwd.Proof.EpilogueSearchWarp
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Step.ExitLast
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputFallbackCuQReadClass
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainCuQReadClass
import all Kernels.TmlFa4Fwd.Proof.Thread.EpilogueLaterDrainCuQRead
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainCuQReadClass
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxFallbackWord
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxMetadataReads
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFallbackWord
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionMetadataReads
import all Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import all Kernels.TmlFa4Fwd.Proof.Thread.RowDrainLaterWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Allocation

/-- Each CuQ read is classified by its role and scheduler or drain operation. -/
inductive CuQLookup (X : Execution) (i : EvId) (a : Acc) (bytes : List (Option Byte)) : Prop
  | initial : InitialCuQRead X i a bytes → CuQLookup X i a bytes
  | loaderGeometry : LoaderCuQRead X i a bytes → CuQLookup X i a bytes
  | loaderFallback : LoaderFallbackCuQRead X i a bytes → CuQLookup X i a bytes
  | loaderFirstDrain : Loader.FirstDrainCuQRead X i a bytes → CuQLookup X i a bytes
  | loaderLaterDrain : Loader.LaterDrainCuQRead X i a bytes → CuQLookup X i a bytes
  | mmaTrip (which : Fin 3) : MmaTripRead.Observed X i which a bytes → CuQLookup X i a bytes
  | mmaFirstDrain : MmaInitialDrainCuQRead X i a bytes → CuQLookup X i a bytes
  | mmaGrouped (group : MmaCuQGroup) : MmaGroupedCuQRead group X i a bytes → CuQLookup X i a bytes
  | outputGeometry : OutputCuQRead X i a bytes → CuQLookup X i a bytes
  | outputFallback : OutputFallbackCuQRead X i a bytes → CuQLookup X i a bytes
  | outputFirstDrain : OutputDrainCuQRead X i a bytes → CuQLookup X i a bytes
  | outputLaterDrain : OutputLaterDrainCuQRead X i a bytes → CuQLookup X i a bytes
  | softmaxGeometry (which : Fin 3) : SoftmaxGeometryRead X i which a bytes → CuQLookup X i a bytes
  | softmaxFallback : SoftmaxFallbackCuQRead X i a bytes → CuQLookup X i a bytes
  | correctionGeometry : CorrectionCuQRead X i a bytes → CuQLookup X i a bytes
  | correctionFallback : CorrectionFallbackCuQRead X i a bytes → CuQLookup X i a bytes
  | rowFirstDrain (role : RowDrainRole) : role.FirstCuQRead X i a bytes → CuQLookup X i a bytes
  | rowLaterDrain (role : RowDrainRole) : role.LaterCuQRead X i a bytes → CuQLookup X i a bytes

/-- The decoded global-load table is covered by the semantic CuQ read classes. -/
theorem MetadataRead.cuQ {X : Execution} {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (h : MetadataRead X i .cuQ a bytes) : CuQLookup X i a bytes := by
  obtain ⟨site, hSite, he⟩ := h
  change site ∈ [186,245,381,382,1750,1805,1940,1999,2112,2113,2653,2707,
    2776,2835,2953,2954,2989,3043,3110,3169,3369,3370,7621,7677,
    7761,7821,7955,7956,9089,9144] at hSite
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .initial ⟨186,by decide,he⟩
  · exact .loaderFallback he
  · exact .loaderGeometry ⟨381,.inl rfl,he⟩
  · exact .loaderGeometry ⟨382,.inr rfl,he⟩
  · exact .loaderFirstDrain he
  · exact .loaderLaterDrain he
  · exact .initial ⟨1940,by decide,he⟩
  · exact .mmaGrouped .fallback (MmaGroupedCuQRead.of_fallback he)
  · exact .mmaTrip 0 he
  · exact .mmaTrip 1 he
  · exact .mmaFirstDrain (MmaInitialDrainCuQRead.of_event he)
  · exact .mmaGrouped .drain (MmaGroupedCuQRead.of_drain he)
  · exact .initial ⟨2776,by decide,he⟩
  · exact .outputFallback he
  · exact .outputGeometry ⟨0,he⟩
  · exact .outputGeometry ⟨1,he⟩
  · exact .outputFirstDrain he
  · exact .outputLaterDrain he
  · exact .initial ⟨3110,by decide,he⟩
  · exact .softmaxFallback he
  · exact .softmaxGeometry 0 he
  · exact .softmaxGeometry 1 he
  · exact .rowFirstDrain .softmax he
  · exact .rowLaterDrain .softmax he
  · exact .initial ⟨7761,by decide,he⟩
  · exact .correctionFallback he
  · exact .correctionGeometry ⟨7955,.inl rfl,he⟩
  · exact .correctionGeometry ⟨7956,.inr rfl,he⟩
  · exact .rowFirstDrain .correction he
  · exact .rowLaterDrain .correction he

end PTX.Kernels.TmlFa4Fwd.Thread

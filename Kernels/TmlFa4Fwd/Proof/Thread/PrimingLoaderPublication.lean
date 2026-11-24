-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.PrimingLoaderActive
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyFacts
public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- An arrive-on for one of the loader's two initial copy packets. -/
def PrimingPublication (l : Launch) (X : Execution) (i : EvId) (slot : Fin 2) : Prop :=
  X.get i = some ⟨copyCommitPc (primingPacketSite slot) + 1,
    .asyncArrive (readyObject l i.1 ⟨slot.val, by have := slot.isLt; omega⟩) true⟩

theorem PrimingPublication.arrive {l : Launch} {X : Execution} {i : EvId} {slot : Fin 2}
    (h : PrimingPublication l X i slot) :
    X.AsyncArrive i (readyObject l i.1 ⟨slot.val, by have := slot.isLt; omega⟩) true :=
  ⟨_, h⟩

theorem PrimingPublication.loaderWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {slot : Fin 2} (h : PrimingPublication l X i slot) :
    14 ≤ warpIndex l i.1 := by
  obtain ⟨lane, hThread⟩ := publicationProducer hp hX h.arrive
  have hBlock : l.block = 512 := hp.block
  have hLane := lane.isLt
  unfold producer readyProducer at hThread
  unfold warpIndex
  rw [hBlock] at hThread ⊢
  rw [hThread]
  omega

private theorem primingPublicationCut (slot : Fin 2) (bound : Nat) :
    let cut := copyCommitPc (primingPacketSite slot) + 2
    ((kernel.code.drop cut).take (1901 - cut)).all
      (fun i => loaderPipelineCutOp cut 1901 bound [2535, 1062] i.op) = true := by
  fin_cases slot <;> exact (by
    set_option maxRecDepth 100000 in kernel_rfl)

private theorem primingPublicationCopySite {site : Fin 6} {pc : Nat}
    (slot : Fin 2) (hLo : copyPacketFirst site ≤ pc)
    (hHi : pc < copyCommitPc (primingPacketSite slot) + 2) :
    site = 0 ∨ site = 1 := by
  fin_cases site <;> fin_cases slot <;>
    norm_num [copyPacketFirst, copyCommitPc, primingPacketSite] at hLo hHi ⊢ <;> omega

/-- The initial value arrival tracks both earlier initial packets. -/
theorem PrimingPublication.trackedVector {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i copy : EvId} {slot : Fin 2} (h : PrimingPublication l X i slot)
    (hTrack : TracksCpAsync X copy i) :
    ∃ (pair : Fin 16) (upper : Bool) (spec : AsyncCopy.Spec),
      PrimingKeyVector X copy pair upper spec ∨ PrimingValueVector X copy pair upper spec := by
  obtain ⟨g, index⟩ := i
  obtain ⟨g', j⟩ := copy
  obtain ⟨hEq, hBefore, ⟨spec, ⟨pc, he⟩, _⟩, _⟩ := hTrack
  change g' = g at hEq
  subst g'
  have hLate : 173 < copyCommitPc (primingPacketSite slot) + 1 := by
    fin_cases slot <;> decide
  have hCut : 174 ≤ copyCommitPc (primingPacketSite slot) + 2 ∧
      copyCommitPc (primingPacketSite slot) + 2 ≤ 1901 := by
    fin_cases slot <;> decide
  have hBeforeCut := eventBeforeClosedCut hp hX (h.loaderWarp hp hX) hCut
    (primingPublicationCut slot) he h (Nat.le_of_lt hBefore) hLate (by simp)
  obtain ⟨hLo, hHi, hCopyPc⟩ := actualCopyAtInLoader hX he
  obtain ⟨site, hFirst, hLast⟩ := loaderCopyPcInPacket hLo hHi hCopyPc
  obtain ⟨pair, upper, hPc⟩ := packetCopyCoordinates site hFirst hLast hCopyPc
  change pc < copyCommitPc (primingPacketSite slot) + 2 at hBeforeCut
  refine ⟨pair, upper, spec, ?_⟩
  have hOffset : (if 8 ≤ pair.val then 1 else 0) =
      (if pair.val < 8 then 0 else 1) := by
    split <;> split <;> omega
  rcases primingPublicationCopySite slot hFirst hBeforeCut with rfl | rfl
  · left
    rw [hPc] at he
    simpa [PrimingKeyVector, packetPlanePc, packetPairPc, copyPacketFirst, kCopyPc,
      hOffset] using he
  · right
    rw [hPc] at he
    simpa [PrimingValueVector, packetPlanePc, packetPairPc, copyPacketFirst, vCopyPc,
      hOffset] using he

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

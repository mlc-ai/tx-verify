-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSingleBiasVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingCopyGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.Kernels.TmlFa4Fwd.Loader Epilogue Prologue

private theorem singleVisitCacheCopyCoordinates {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {i : EvId} {s : AsyncCopy.Spec} {batch : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ i.1 / l.block)
    (hHi : i.1 / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (i.1 / l.block)).1 = 1)
    (hCopy : X.Copy i s) :
    ∃ (stage : Fin 2) (pair : Fin 16) (upper : Bool),
      X.get i = some ⟨packetPlanePc (primingPacketSite stage) pair upper, .copy s⟩ ∧
      14 ≤ warpIndex l i.1 ∧
      let addr := kvCopyAddress l.sharedBase stage (i.1 % l.block) pair upper
      s.dst = {loc := ⟨.shared, i.1 / l.block, addr⟩, size := 16} := by
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, he⟩ := hCopy
  obtain ⟨hLow, hHigh, hCode⟩ := actualCopyAtInLoader hX he
  obtain ⟨site, hFirst, hLast⟩ := loaderCopyPcInPacket hLow hHigh hCode
  have hBounds : 550 ≤ pc ∧ pc < 1744 := by
    have hSiteBounds : 550 ≤ copyPacketFirst site ∧ copyCommitPc site < 1744 := by
      fin_cases site <;> decide
    omega
  have hEarly : pc < 905 := by
    by_contra! hLate
    exact singleVisitLoaderEventNotRecurring hp hX hDone hb hLo hHi hTrip
      (fun _ _ _ _ => loaderOutputWrites hFrame) he ⟨hLate, hBounds.2⟩
      (by simp [Ends])
  have hPriming : site.val < 2 := by
    fin_cases site <;> first | decide | (simp [copyPacketFirst] at hFirst; omega)
  let stage : Fin 2 := ⟨site.val, hPriming⟩
  have hSite : site = primingPacketSite stage := Fin.ext rfl
  obtain ⟨pair, upper, rfl⟩ := actualPacketCopyCoordinates hX site hFirst hLast he
  rw [hSite] at he hFirst hLast hBounds
  obtain ⟨_, q, vs, _, hAt, hWalk, hSeen⟩ :=
    actualPrimingCopyCheckpoint hp hX stage he hFirst hLast
  have hDst := primingCopyDestinationFromEntry hp stage pair upper hAt hWalk
    (List.mem_of_getElem? hSeen)
  have hHint : packetPlanePc (primingPacketSite stage) pair upper ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he
    (show 173 < packetPlanePc (primingPacketSite stage) pair upper by omega) hHint
  change roleBodyPc (warpIndex l g) (packetPlanePc (primingPacketSite stage) pair upper) at hRole
  have hWarp : 14 ≤ warpIndex l g := by
    rcases hRole with he | he
    · omega
    · split_ifs at he <;> omega
  exact ⟨stage, pair, upper, he, hWarp, hDst⟩

/-- A single-visit CTA has at most one issued cache copy covering a shared byte. -/
theorem singleVisitCacheCopyUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {first other : EvId} {s t : AsyncCopy.Spec} {batch : Nat} {loc : Loc}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ first.1 / l.block)
    (hHi : first.1 / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (first.1 / l.block)).1 = 1)
    (hFirst : X.Copy first s) (hOther : X.Copy other t)
    (hCover : s.dst.Covers loc) (hCovers : t.dst.Covers loc) : other = first := by
  have hCta : other.1 / l.block = first.1 / l.block := by
    obtain ⟨_, _, _, _, hDstA⟩ := copyDestination hp hX hFirst
    obtain ⟨_, _, _, _, hDstB⟩ := copyDestination hp hX hOther
    have hLocA := hCover.2.1
    have hLocB := hCovers.2.1
    rw [hDstA] at hLocA
    rw [hDstB] at hLocB
    exact hLocB.symm.trans hLocA
  obtain ⟨stage, pair, upper, he, hWarp, hDst⟩ :=
    singleVisitCacheCopyCoordinates hp hX hDone hFrame hb hLo hHi hTrip hFirst
  obtain ⟨otherStage, otherPair, otherUpper, hf, hWarp', hDst'⟩ :=
    singleVisitCacheCopyCoordinates hp hX hDone hFrame hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi)
      (hCta.symm ▸ hTrip) hOther
  rw [hDst] at hCover
  rw [hDst'] at hCovers
  let a := kvCopyAddress l.sharedBase stage (first.1 % l.block) pair upper
  let b := kvCopyAddress l.sharedBase otherStage (other.1 % l.block) otherPair otherUpper
  have hAddr : a ≤ loc.addr ∧ loc.addr < a + 16 := hCover.2.2
  have hAddr' : b ≤ loc.addr ∧ loc.addr < b + 16 := hCovers.2.2
  have hSame : stage.val = otherStage.val ∧ first.1 % l.block % 64 = other.1 % l.block % 64 ∧
      pair.val = otherPair.val ∧ upper = otherUpper := by
    by_contra! hApart
    have hDifferent : stage.val ≠ otherStage.val ∨
        first.1 % l.block % 64 ≠ other.1 % l.block % 64 ∨
        pair.val ≠ otherPair.val ∨ upper ≠ otherUpper := by
      by_cases hStage : stage.val = otherStage.val
      · by_cases hLane : first.1 % l.block % 64 = other.1 % l.block % 64
        · by_cases hPair : pair.val = otherPair.val
          · exact .inr (.inr (.inr (hApart hStage hLane hPair)))
          · exact .inr (.inr (.inl hPair))
        · exact .inr (.inl hLane)
      · exact .inl hStage
    have hVector := kvCopyVectorsApart hp.shared.1 pair.isLt otherPair.isLt hDifferent
    change a + 16 ≤ b ∨ b + 16 ≤ a at hVector
    omega
  obtain ⟨hStages, hLane, hPairs, hUpper⟩ := hSame
  have hStage : otherStage = stage := Fin.ext hStages.symm
  have hPair : otherPair = pair := Fin.ext hPairs.symm
  subst otherStage otherPair otherUpper
  have hLocal : first.1 % l.block = other.1 % l.block := by
    change 14 ≤ first.1 % l.block / 32 at hWarp
    change 14 ≤ other.1 % l.block / 32 at hWarp'
    rw [hp.block] at hWarp hWarp' hLane ⊢
    omega
  have hThread : other.1 = first.1 := by
    have hA := Nat.div_add_mod first.1 l.block
    have hB := Nat.div_add_mod other.1 l.block
    rw [hCta, ← hLocal] at hB
    omega
  have hStation : (550 ≤ packetPlanePc (primingPacketSite stage) pair upper ∧
      packetPlanePc (primingPacketSite stage) pair upper ≤ 672) ∨
      (810 ≤ packetPlanePc (primingPacketSite stage) pair upper ∧
        packetPlanePc (primingPacketSite stage) pair upper ≤ 902) := by
    fin_cases stage <;> fin_cases pair <;> cases upper <;> decide
  have hf' : X.get (first.1, other.2) =
      some ⟨packetPlanePc (primingPacketSite stage) pair upper, .copy t⟩ := by
    rw [← hThread]
    exact hf
  exact Prod.ext hThread (uniquePrimingCopy hp hX hWarp hStation hf' he)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

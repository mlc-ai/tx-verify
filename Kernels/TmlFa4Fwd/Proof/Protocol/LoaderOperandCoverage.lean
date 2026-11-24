-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy
public import Kernels.TmlFa4Fwd.Proof.MmaPvInputLayout
public import Kernels.TmlFa4Fwd.Proof.MmaQkKeyLayout
public import Kernels.TmlFa4Fwd.Proof.Protocol.MmaReadyConsumer
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.Thread.MmaOperandReady
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (CachePlane PublishedCopyGroup producer producerLaneMod)
open Mma (qkOperands pvOperands kvSlot qkByteIndex qkLoaderLane qkLoaderByte pvKeyRow)
open Loader (kvUseStage)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {wait mma : EvId} {slot : Fin 3}
    {phase d index : Nat} {isB accum : Bool} {mask : List Nat} {op : TcMma.OperandSpec} {loc : Loc}
    (h : Completed l X wait slot phase) (lane : Fin 64) (pair : Fin 16) (upper : Bool) {off : Nat}
    (hOff : off < 16) (hMma : X.MmaIssue mma d op accum mask) (hEarlier : TraceBefore X wait mma)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc)
    (hVector : loc =
      ⟨.shared, wait.1 / l.block,
        kvCopyAddress l.sharedBase slot lane pair upper + off⟩)
include hp hX h lane pair upper hOff hMma hEarlier hLoc hVector

/-- Every operand byte of the observed slot with a loader vector coordinate has
an actual covering write from the selected generation, ordered before its MMA read. -/
theorem Completed.actualOperandCoveringCopyWithPublication :
    ∃ (issue : EvId) (group : PublishedCopyGroup l X issue) (j : Nat) (spec : Spec)
        (bytes : List Byte),
      X.AsyncArrive issue (Thread.Loader.readyObject l wait.1 slot) true ∧
      issue.1 = producer l (wait.1 / l.block) lane ∧
      generation l X issue slot = phase ∧ group.publication.slot = slot ∧
      group.publication.packet.plane = (if (3 * phase + slot.val) % 2 = 0 then .key else .value) ∧
      (j, spec) ∈ group.copies ∧ spec.dst.loc.at off = loc ∧ spec.dst.Covers loc ∧
      X.MemWrites (.async (issue.1, j) (.write .copy)) spec.dst bytes ∧
      modelCausality l X loc (.async (issue.1, j) (.write .copy))
        (.async mma (.mmaRead isB index)) := by
  obtain ⟨issue, group, hLane, hPub, hPhase, hCopies⟩ :=
    h.actualCopyGroupBeforeOperand hp hX lane hMma hEarlier hLoc
  have hSlot := group.slotFor hp hX hPub
  have hPlane := Thread.Loader.publicationPlaneOfGeneration hp hX hPub group.published
  change group.publication.packet.plane =
    (if (3 * generation l X issue group.publication.slot + group.publication.slot.val) % 2 = 0
      then .key else .value) at hPlane
  rw [hSlot, hPhase] at hPlane
  have hCta := publicationCta hp hX hPub
  obtain ⟨j, spec, hj, hDst⟩ := group.coverage hp hX hPub pair upper
  have hProducerLane := producerLaneMod hp (wait.1 / l.block) lane
  have hExact : spec.dst =
      {loc := ⟨.shared, wait.1 / l.block, kvCopyAddress l.sharedBase slot lane pair upper⟩,
        size := 16} := by
    dsimp only at hDst
    rw [hSlot, ← hCta, hLane] at hDst
    simpa only [kvCopyAddress, hProducerLane, Nat.mod_eq_of_lt lane.isLt] using hDst
  have hOffLoc : spec.dst.loc.at off = loc := by rw [hExact, hVector]; rfl
  have hCover : spec.dst.Covers loc := by
    rw [hVector, hExact]
    simp only [Acc.Covers, Loc.InRange, true_and]
    omega
  obtain ⟨⟨bytes, hw⟩, hOrder⟩ := hCopies j spec hj hCover
  exact ⟨issue, group, j, spec, bytes, hPub, hLane, hPhase, hSlot, hPlane, hj, hOffLoc, hCover,
    hw, hOrder⟩

end

/-- Both MMA contractions use the ordinary cache ring for their B operand. -/
noncomputable def cacheOperand (l : Launch) (g : Nat) (block : Fin 4) (step : Fin 8)
    (use : Nat) : CachePlane → TcMma.OperandSpec
  | .key => qkOperands l g block step use
  | .value => pvOperands l g block step use

/-- The two bytes of an MMA cache element use one aligned word of one loader vector. -/
theorem cacheOperandWordVector {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat) (plane : CachePlane)
    {row k : Nat} (hr : row < 128) (hk : k < 16) :
    ∃ (lane : Fin 64) (pair : Fin 16) (upper : Bool) (word : Nat), word < 8 ∧
      ∀ byte : Fin 2,
      (cacheOperand l g block step use plane).byteLoc .b (qkByteIndex row k byte) = some
        ⟨.shared, g / l.block,
          kvCopyAddress l.sharedBase (kvUseStage use) lane pair upper + (2 * word + byte.val)⟩ := by
  cases plane
  case key =>
    have hc := Mma.qkPlaneColumn_lt step hk
    have hLane : qkLoaderLane step row k < 64 := by unfold qkLoaderLane; omega
    let word := Mma.qkPlaneColumn step k % 8
    exact ⟨⟨_, hLane⟩, ⟨row / 8, by omega⟩, decide (4 ≤ step.val), word,
      Nat.mod_lt _ (by decide), fun b => Mma.qkKCopyByteLoc l g block step use hp.shared.1
        hr hk b.isLt⟩
  case value =>
    have hKey : pvKeyRow step k < 128 := by unfold pvKeyRow; have := step.isLt; omega
    let lane := 8 * (pvKeyRow step k % 8) + (row % 64) / 8
    have hLane : lane < 64 := by dsimp [lane]; omega
    refine ⟨⟨lane, hLane⟩, ⟨pvKeyRow step k / 8, by omega⟩, decide (64 ≤ row),
      row % 8, Nat.mod_lt _ (by decide), fun b => ?_⟩
    simpa only [Nat.add_assoc, cacheOperand, lane, Loader.kvUseStage_val, kvSlot] using
      Mma.pvValueByteLoc l g block step use hp.shared.1 hr hk b.isLt

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A byte on one slot and generation has at most one covering copy among
the actual publications of that slot. -/
theorem coveringCopyUniqueInGeneration {a b : EvId} {owner : Nat} {slot : Fin 3}
    (ga : PublishedCopyGroup l X a) (gb : PublishedCopyGroup l X b)
    (ha : X.AsyncArrive a (Thread.Loader.readyObject l owner slot) true)
    (hb : X.AsyncArrive b (Thread.Loader.readyObject l owner slot) true)
    (hRank : generation l X a slot = generation l X b slot) {i j : Nat} {sa sb : Spec} {loc : Loc}
    (hai : (i, sa) ∈ ga.copies) (hbj : (j, sb) ∈ gb.copies) (hca : sa.dst.Covers loc)
    (hcb : sb.dst.Covers loc) :
    a = b ∧ i = j := by
  have hApart := Loader.noCpAsyncOverlap hp hX
  obtain ⟨hIssuer, _⟩ :=
    Thread.Loader.copiesSharingSlotByteSameIssuer hp hX ga gb ha hb hai hbj hca hcb
  have hSame := Thread.Loader.publicationUniqueAtSlot hp hX ha hb hIssuer hRank
  subst b
  have hCommit : ga.commit = gb.commit := by
    have hA := ga.closesAt
    have hB := gb.closesAt
    omega
  obtain ⟨hiFirst, hiCommit, hiCopy⟩ := (ga.member i sa).mp hai
  obtain ⟨hjFirst, hjCommit, hjCopy⟩ := (gb.member j sb).mp hbj
  refine ⟨rfl, ?_⟩
  by_contra hNe
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hLt
  · have hJ : (j, sb) ∈ ga.copies :=
      (ga.member j sb).mpr ⟨by omega, by omega, hjCopy⟩
    exact hApart ⟨(a.1, i), (a.1, j), sa, sb, ga.sameGroup hai hJ hLt,
      hiCopy, hjCopy, loc, hca, hcb⟩
  · have hI : (i, sa) ∈ gb.copies :=
      (gb.member i sa).mpr ⟨by omega, by omega, hiCopy⟩
    exact hApart ⟨(a.1, j), (a.1, i), sb, sa, gb.sameGroup hbj hI hLt,
      hjCopy, hiCopy, loc, hcb, hca⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasIssueOrigin
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlotGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import Lemmas.Tensor.TensorTransfer

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.AsyncCopy PTX.Kernels.TmlFa4Fwd.Loader Thread.Loader
open Softmax Epilogue Protocol.Bias

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem ordinaryWriteBelowBias {i : EvId} {a : Acc} {loc : Loc} {data : List Byte}
    (hWrite : X.Writes i a data) (hCover : a.Covers loc) (hShared : loc.space = .shared) :
    loc.addr < l.sharedBase + 166912 := by
  rcases ordinarySharedWriteBelowOrStaging hp hX hWrite hCover hShared with hLow | hStaging
  · omega
  obtain ⟨stage, box, chunk, he⟩ := hStaging.decoded
  obtain ⟨element, hAcc⟩ := Correction.stagingWriteElement hp hX stage box chunk he
  rw [hAcc] at hCover
  have hx : 4 * chunk.val + element.val < 32 := by
    have := chunk.isLt
    have := element.isLt
    omega
  have hUpper : loc.addr < l.sharedBase + 3072 + 65536 * (stage.val + 1) :=
    (Thread.Output.elementStageRange hx (Nat.mod_lt _ (by decide)) hCover).2
  have hCap := (by decide : ∀ stage : Fin 2, 3072 + 65536 * (stage.val + 1) ≤ 166912) stage
  exact hUpper.trans_le (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hCap _)

private theorem cacheCopyBelowBias {i : EvId} {s : AsyncCopy.Spec} {loc : Loc} (hCopy : X.Copy i s)
    (hCover : s.dst.Covers loc) : loc.addr < l.sharedBase + 166912 := by
  obtain ⟨pc, he⟩ := hCopy
  obtain ⟨hLo, hHi, hAt⟩ := actualCopyAtInLoader hX he
  obtain ⟨site, hlo, hhi⟩ := loaderCopyPcInPacket hLo hHi hAt
  obtain ⟨pair, upper, rfl⟩ := actualPacketCopyCoordinates hX site hlo hhi he
  rcases i with ⟨g, j⟩
  obtain ⟨slot, hDst⟩ := actualCopyPrefixDestination hp hX site pair upper he
  rw [hDst] at hCover
  obtain ⟨_, _, hLo, hHi⟩ := hCover
  have hByte : loc.addr - kvCopyAddress l.sharedBase slot (g % l.block) pair upper < 16 := by
    change loc.addr < kvCopyAddress l.sharedBase slot (g % l.block) pair upper + 16 at hHi
    omega
  have hUpper := (kvCopyAddress_range (lane := g % l.block) (upper := upper)
    hp.shared.1 slot.isLt pair.isLt hByte).2
  change kvCopyAddress l.sharedBase slot (g % l.block) pair upper ≤ loc.addr at hLo
  omega

/-- Every performed write into a Bias buffer is one byte of an input TMA. -/
theorem biasWriteSource {w : Ref} {a : Acc} {data : List Byte} {loc : Loc}
    (hWrite : X.MemWrites w a data) (hCover : a.Covers loc) (hShared : loc.space = .shared)
    (hLo : l.sharedBase + 166912 ≤ loc.addr) :
    ∃ tensor x y byte, w = .async tensor (.write (.load x y byte)) := by
  rcases sharedWriteSource hX hWrite hCover hShared with
    ⟨i, _, hOrd⟩ | hInput | ⟨i, s, _, hCopy, rfl⟩
  · have hLt := ordinaryWriteBelowBias hp hX hOrd hCover hShared
    omega
  · exact hInput
  · have hLt := cacheCopyBelowBias hp hX hCopy hCover
    omega

omit hp hX in
private theorem inputWriteInSubbox {p : Params} {site : Fin 14} {s : TensorCopy.Spec}
    {x y byte : Nat} {loc : Loc}
    (hDesc : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨2, inputMap p (inputSite site)⟩)
    (hWrite : TensorCopy.writeLoc s x y byte = some loc) :
    s.sharedBase.InRange 16384 loc := by
  rcases s with ⟨⟨outer, desc, origin, base, rows⟩, barrier, cluster, group⟩
  simp only [Sigma.mk.injEq] at hDesc
  obtain ⟨rfl, hMap⟩ := hDesc
  obtain rfl := eq_of_heq hMap
  let d := inputMap p (inputSite site)
  have hShape : d.format.bytes = 2 ∧ d.swizzle = .b128 ∧
      TensorTile.count d.box 0 = 64 ∧ TensorTile.rows d.box = 128 := by
    dsimp [d]
    cases hBias : (inputSite site).bias <;>
      norm_num [inputMap, hBias, Params.biasMap, Params.qMap, TensorTile.count,
        TensorTile.step, TensorTile.rows, TensorTile.rowsOf, TensorDescriptor.Format.bytes]
  obtain ⟨hBytes, hSwizzle, hCols, hRows⟩ := hShape
  obtain ⟨slot, _, rfl⟩ := Option.map_eq_some_iff.mp hWrite
  have hWidth : TensorTile.count d.box 0 * d.format.bytes = 128 := by rw [hCols, hBytes]
  obtain ⟨offset, hLt, hOffset⟩ := tensorSharedBoxOffset (base := base.addr) hSwizzle hWidth
    slot.1.isLt slot.2.1.isLt slot.2.2.isLt
  rw [hRows] at hLt
  let addr := TensorTile.sharedByte d.box d.format.bytes d.swizzle base.addr
    slot.1.val slot.2.1.val slot.2.2.val
  change base.InRange 16384 {base with addr := addr}
  rw [show addr = base.addr + offset from hOffset]
  exact ⟨rfl, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left hLt _⟩

/-- An actual input write covering a Bias slot belongs to that physical stage and half. -/
theorem biasWriterOfHalf {g : Nat} {stage half : Fin 2} {writer : EvId} {spec : TensorCopy.Spec}
    {address x y byte : Nat} {loc : Loc} (hIssue : X.TensorIssue writer address spec)
    (hWrite : TensorCopy.writeLoc spec x y byte = some loc)
    (hLoc : (⟨.shared, g / l.block, biasBoxStart l stage half.val⟩ : Loc).InRange 16384 loc) :
    writer.1/l.block = g/l.block ∧ BiasSubbox p l X writer stage half spec := by
  obtain ⟨_, he⟩ := hIssue
  obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
  have hIssue : X.TensorIssue writer address spec := ⟨_, he⟩
  obtain ⟨_, hDesc, _, hDst, _, _⟩ := actualInputBoxAt hp hX site he
  have hRange := inputWriteInSubbox hDesc hWrite
  rw [hDst] at hRange
  have hOwner : writer.1 / l.block = g / l.block := hRange.2.1.symm.trans hLoc.2.1
  have hOf : (inputSite site).sharedOffset = 166912 + 32768 * stage.val + 16384 * half.val := by
    have hAddr1 := hRange.2.2
    have hAddr2 := hLoc.2.2
    change l.sharedBase + (inputSite site).sharedOffset ≤ loc.addr ∧
      loc.addr < l.sharedBase + (inputSite site).sharedOffset + 16384 at hAddr1
    simp only [biasBoxStart] at hAddr2
    fin_cases stage <;> fin_cases half <;> fin_cases site <;>
      simp only [inputSite] at hAddr1 hAddr2 ⊢ <;> omega
  have hMbar := loaderTensorOffset hp hX site he
  have hBarrier : inputBarrierBase site + (inputSite site).barrierOffset = 320 + 8 * stage.val := by
    fin_cases stage <;> fin_cases half <;> fin_cases site <;>
      simp [inputBarrierBase, inputSite] at hOf ⊢
  have hReady : spec.mbar = biasReadyObject l (g / l.block) stage := by
    rw [hMbar, hOwner, hBarrier]
    rfl
  obtain ⟨_, half', hOther⟩ := biasSubboxOfBarrier hp hX stage hIssue hReady
  have hHalf : half' = half := by
    have hAddr := congrArg Loc.addr (hDst.symm.trans hOther.2.2.1)
    change l.sharedBase + (inputSite site).sharedOffset =
      l.sharedBase + (166912 + 32768 * stage.val + 16384 * half'.val) at hAddr
    rw [hOf] at hAddr
    exact Fin.ext (by omega)
  subst half'
  exact ⟨hOwner,hOther⟩

/-- The completed single-visit stage has exactly one actual tensor capable of writing a
byte of its selected physical half. -/
theorem oneVisitBiasWriter (hComplete : Complete l X) {batch g wait : Nat} {stage half : Fin 2}
    {tensor : EvId} {o : TensorCopy.Observation} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hBox : AcquiredBiasBox p l X stage g wait tensor half o) {writer : EvId}
    {spec : TensorCopy.Spec} {address x y byte : Nat} {loc : Loc}
    (hIssue : X.TensorIssue writer address spec)
    (hWrite : TensorCopy.writeLoc spec x y byte = some loc)
    (hLoc : (⟨.shared, g / l.block, biasBoxStart l stage half.val⟩ : Loc).InRange 16384 loc) :
    writer = tensor := by
  obtain ⟨hOwner,hOther⟩ := biasWriterOfHalf hp hX hIssue hWrite hLoc
  obtain ⟨_,hGet⟩ := hOther.1
  have hPriming := singleVisitInputIssueIsPriming hp hX hComplete hb (hOwner.symm ▸ hLo)
    (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrip) writes hGet
  obtain ⟨selPc, hSel⟩ := hBox.issue
  have hSelected := hBox.owner
  have hSelPr := singleVisitInputIssueIsPriming hp hX hComplete hb (hSelected.symm ▸ hLo)
    (hSelected.symm ▸ hHi) (hSelected.symm ▸ hTrip) writes hSel
  by_contra hNe
  exact primingBiasSubboxHalvesDistinct hp hX (hOwner.trans hSelected.symm) hNe hOther
    hBox.subbox hPriming hSelPr hGet hSel rfl

/-- A covering write is the selected transfer's exact byte, or has the order
proved for another transfer of the same physical half. -/
theorem biasWordOrderForRound {g wait j : Nat} {stage : Fin 2} {tensor : EvId}
    {o : TensorCopy.Observation} (repeated : Bool) (i : Fin 16) (word : Fin 4)
    (hBox : AcquiredBiasBox p l X stage g wait tensor (biasVectorHalf i) o)
    (hOrder : ∀ (byte : Fin 4) writer spec x y k loc,
      BiasSubbox p l X writer stage (biasVectorHalf i) spec → writer.1/l.block = g/l.block →
      TensorCopy.writeLoc spec x y k = some loc →
      (⟨.shared,g/l.block,biasBoxStart l stage (biasVectorHalf i).val⟩ : Loc).InRange 16384 loc →
      AsyncCovers X writer (.write (.load x y k)) loc →
      (∃ part, biasWordWriter p l g i word byte tensor = .async tensor part ∧
        AsyncCovers X tensor part loc) →
      writer = tensor ∨
        modelCausality l X loc (.async writer (.write (.load x y k)))
          (biasWordWriter p l g i word byte tensor) ∨
        modelCausality l X loc (.thread (g,j)) (.async writer (.write (.load x y k)))) :
    BiasWordOrder p l X stage repeated i word g j tensor := by
  intro byte w a data hWrite
  let loc := (biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val).loc.at
    byte.val
  change a.Covers loc → _
  intro hCover
  rcases o with ⟨⟨⟨outer, desc, origin, base, rows⟩, barrier, cluster, group⟩, effects⟩
  have hMap := hBox.descriptor
  simp only [Sigma.mk.injEq] at hMap
  obtain ⟨rfl, hd⟩ := hMap
  obtain rfl := eq_of_heq hd
  have hBase := hBox.destination
  change base = ⟨.shared, g / l.block, biasBoxStart l stage (i.val / 8)⟩ at hBase
  subst base
  let box : TensorCopy.Spec := ⟨⟨2, p.biasMap, origin,
    ⟨.shared, g / l.block, biasBoxStart l stage (i.val / 8)⟩, rows⟩, barrier, cluster, group⟩
  let slot := biasVectorSlot p l g i word byte
  have hReadLoc : loc = box.sharedLoc slot :=
    biasVectorMatchesBox p l g stage repeated i word byte
    origin
  have hReadWriteLoc : TensorCopy.writeLoc box slot.1.val slot.2.1.val slot.2.2.val = some loc := by
    unfold TensorCopy.writeLoc
    rw [TensorCopy.slotAt_self]
    exact congrArg some hReadLoc.symm
  have hMap :
      (⟨box.outer, box.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
        ⟨2, inputMap p (inputSite (2 : Fin 14))⟩ := rfl
  have hRange := inputWriteInSubbox hMap hReadWriteLoc
  have hLower : l.sharedBase + 166912 ≤ loc.addr := by
    have h := hRange.2.2.1
    change biasBoxStart l stage (i.val / 8) ≤ loc.addr at h
    unfold biasBoxStart at h
    omega
  obtain ⟨writer, x, y, k, rfl⟩ := biasWriteSource hp hX hWrite hCover hRange.1 hLower
  have hRecord := hWrite
  obtain ⟨other, address, value, hSeen, hIssue, hWriteLoc, _, hSize, _⟩ := hRecord
  rw [Acc.loc_of_one hCover hSize] at hWriteLoc
  obtain ⟨hOwner,hOther⟩ := biasWriterOfHalf hp hX (g := g) (stage := stage)
    (half := biasVectorHalf i) hIssue hWriteLoc hRange
  let part := Part.write (.load slot.1.val slot.2.1.val slot.2.2.val)
  let target : Acc := {loc := loc, size := 1}
  have hSelected : AsyncCovers X tensor part loc :=
    ⟨target,true,⟨rfl,box,p.biasMapAddress,hBox.issue,hReadWriteLoc,rfl⟩,
      by simp [Acc.Covers,Loc.InRange,target]⟩
  rcases hOrder byte writer other.spec x y k loc hOther hOwner hWriteLoc hRange
      ⟨a,true,hWrite.intent,hCover⟩ ⟨part,rfl,hSelected⟩ with hWriter | hOlder | hLater
  swap
  · exact .inr (.inl hOlder)
  swap
  · exact .inr (.inr hLater)
  subst writer
  have hObserver : other = ⟨box, effects⟩ :=
    Option.some.inj (hSeen.symm.trans hBox.completion)
  subst other
  change TensorCopy.writeLoc box x y k = some loc at hWriteLoc
  obtain ⟨wslot, hSlot, hwLoc⟩ := Option.map_eq_some_iff.mp hWriteLoc
  have hEq := TensorTransfer.sharedByte_injective p.biasMap box.sharedBase.addr
    (congrArg Loc.addr (hwLoc.trans hReadLoc))
  subst wslot
  obtain ⟨rfl, rfl, rfl⟩ := TensorCopy.slotAt_coordinates hSlot
  exact .inl rfl

/-- A covering write is the selected transfer's exact byte, or has the order
proved for another transfer of the same physical half. -/
theorem biasWordOrderOfOverlappingWrites {g wait j : Nat} {stage : Fin 2} {tensor : EvId}
    {o : TensorCopy.Observation} (i : Fin 16) (word : Fin 4)
    (hBox : AcquiredBiasBox p l X stage g wait tensor (biasVectorHalf i) o)
    (hOrder : ∀ writer spec x y k loc,
      BiasSubbox p l X writer stage (biasVectorHalf i) spec → writer.1/l.block = g/l.block →
      TensorCopy.writeLoc spec x y k = some loc →
      (⟨.shared,g/l.block,biasBoxStart l stage (biasVectorHalf i).val⟩ : Loc).InRange 16384 loc →
      AsyncCovers X writer (.write (.load x y k)) loc →
      writer = tensor ∨
        modelCausality l X loc (.thread (g,j)) (.async writer (.write (.load x y k)))) :
    BiasWordOrder p l X stage false i word g j tensor := by
  apply biasWordOrderForRound hp hX false i word hBox
  intro byte writer spec x y k loc hIssue hOwner hLocation hRange hCover _
  exact (hOrder writer spec x y k loc hIssue hOwner hLocation hRange hCover).imp id Or.inr

/-- The single-visit Bias reads have a unique actual writer for each word byte. -/
theorem singleVisitBiasWordOrder (hComplete : Complete l X) {batch g wait j : Nat} {stage : Fin 2}
    {tensor : EvId} {o : TensorCopy.Observation} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) (i : Fin 16) (word : Fin 4)
    (hBox : AcquiredBiasBox p l X stage g wait tensor (biasVectorHalf i) o) :
    BiasWordOrder p l X stage false i word g j tensor := by
  apply biasWordOrderOfOverlappingWrites hp hX i word hBox
  intro writer spec x y k loc hOther _ hWrite hLoc _
  exact .inl (oneVisitBiasWriter hp hX hComplete hb hLo hHi hTrip writes hBox hOther.1 hWrite hLoc)
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X) {batch g wait : Nat}
    {stage : Fin 2} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hX hComplete hb hLo hHi hTrip writes

/-- The initial Bias acquire selects the two actual single-visit copies, with both their
descriptor coordinates and byte provenance determined by the execution. -/
theorem singleVisitFirstBiasSources (hWait : FirstBiasAcquire l X g wait stage) :
    let coords := assignedCoordinates p batch (g / l.block)
    ∃ tensor : Fin 2 → EvId,
      (∀ half, FirstBiasBox p l X stage g wait (firstVisitBiasBoxColumn half)
        (p.qOffset batch + 128 * (2 * coords.1 + stage.val)) coords.2 half (tensor half)) ∧
      (∀ i (word : Fin 4),
        BiasWordOrder p l X stage false i word g (wait + 1 + 4 * i.val + word.val)
          (tensor (biasVectorHalf i))) := by
  obtain ⟨_, _, tensor, _, hBoxes⟩ :=
    singleVisitFirstBiasBoxes hp hX hComplete hb hLo hHi hTrip writes hWait
  exact ⟨tensor,
    fun half => singleVisitFirstBiasBoxOfAcquire hp hX hComplete hb hLo hHi hTrip writes
      (hBoxes half).2,
    fun i word => singleVisitBiasWordOrder hp hX hComplete hb hLo hHi hTrip writes i word
      (hBoxes (biasVectorHalf i)).2⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores

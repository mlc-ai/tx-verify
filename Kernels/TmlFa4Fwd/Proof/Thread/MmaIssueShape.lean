-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Core.Tc.TcMmaSafety
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.QkIssueFlags
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyProbabilityColumn
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX.TcMma PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem sharedEncoded {start lead : Nat} (hStart : start < 2 ^ 18)
    (hAlign : start % 16 = 0) (hLead : lead = 16 ∨ lead = 16384) :
    SharedEncoded (sharedDescriptor start lead) := by
  rcases hLead with rfl | rfl <;> simp only [SharedEncoded, sharedDescriptor] <;>
    exact ⟨hStart, by decide, by decide, hAlign, by decide, by decide⟩

private theorem queryEncoded {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) (step : Fin 8) :
    SharedEncoded (sharedDescriptor (qStart l stage + qkFragment step) 16) := by
  have hBase := hp.shared.1
  have hBound := hp.shared.2.1
  have hs := stage.isLt
  have hj := step.isLt
  apply sharedEncoded (hLead := .inl rfl) <;> simp only [qStart, qkFragment] <;> omega

private theorem cacheEncoded {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (use : Nat) (step : Fin 8) (isKey : Bool) :
    SharedEncoded (sharedDescriptor
      (kvStart l use + if isKey then qkFragment step else pvFragment step)
      (if isKey then 16 else 16384)) := by
  have hBase := hp.shared.1
  have hBound := hp.shared.2.1
  have hs := Nat.mod_lt use (show 0 < 3 by decide)
  have hj := step.isLt
  cases isKey <;> apply sharedEncoded
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | simp only [Bool.false_eq_true, ite_false, ite_true, kvStart, kvSlot,
        pvFragment, qkFragment] ; omega

private theorem qkZeroMask {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {block : Fin 4} {frag : Fin 8} {d : Nat} {s : OperandSpec}
    {accum : Bool} {mask : List Nat} (hi : QkInstruction X i block frag d s accum mask) :
    mask = List.replicate 4 0 := by
  have he := hi.decoded
  obtain ⟨_, hr⟩ := hX.thr i.1 (event_thread_lt hX he)
  obtain ⟨t, o, _, hStep⟩ := hr.before_event he
  cases o with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    rcases PTX.Flow.fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    exact (qkStepFields block frag (dst := none) (by simp) hStep).2.2

private theorem qkAddresses {l : Launch} {g use : Nat} {block : Fin 4} {frag : Fin 8}
    {s : OperandSpec} (hQ : QueryOperandFragment l g (qkStage block) frag s)
    (hB : s.b = sharedDescriptor (kvStart l use+qkFragment frag) 16)
    (op : Operand) (index : Nat) (hi : index < op.bytes s.descriptor) :
    ∃ loc, s.byteLoc op index = some loc := by
  have hv : Valid qkDescriptor := by decide
  unfold qkDescriptor at hv
  have hRows : index / 32 < 128 := by
    rw [hQ.descriptor] at hi
    have hn : op.bytes qkDescriptor = 4096 := by cases op <;> decide
    rw [hn] at hi
    omega
  have hByte : index % 2 < 2 := Nat.mod_lt _ (by decide)
  cases op <;>
    simp [OperandSpec.byteLoc, hQ.descriptor, hQ.shared, hQ.address, hB, hv, qkDescriptor,
      Operand.extent, Operand.major, Kind.k, Kind.width, hRows, sharedDescriptor,
      TcShared.byteAddress, hByte]

private theorem pvAddresses {l : Launch} {use addr : Nat} {frag : Fin 8}
    {s : OperandSpec} (hDesc : s.descriptor = pvDescriptor)
    (hB : s.b = sharedDescriptor (kvStart l use+pvFragment frag) 16384)
    (hA : s.aTmem = some addr) (hSmall : addr + 8 ≤ 512)
    (op : Operand) (index : Nat) (hi : index < op.bytes s.descriptor) :
    (∃ loc, s.byteLoc op index = some loc) ∨ (op = .a ∧ ∃ c, aCell s index = some c) := by
  have hv : Valid pvDescriptor := by decide
  unfold pvDescriptor at hv
  have hRows : index / 32 < 128 := by
    rw [hDesc] at hi
    have hn : op.bytes pvDescriptor = 4096 := by cases op <;> decide
    rw [hn] at hi
    omega
  have hByte : index % 2 < 2 := Nat.mod_lt _ (by decide)
  cases op with
  | a =>
    right
    refine ⟨rfl, ?_⟩
    have hLane : addr < 65536 := by omega
    have hMod : addr % 65536 = addr := Nat.mod_eq_of_lt hLane
    have hFit : addr ≤ 504 := by omega
    simp [aCell, hDesc, hA, hv, pvDescriptor, Operand.rows, Operand.extent, Kind.k, Kind.width,
      halfDatapath, CtaGroup.size, hLane, hMod, hFit, hRows]
  | b =>
    left
    simp [OperandSpec.byteLoc, hDesc, hB, hv, pvDescriptor, Operand.extent, Operand.major,
      Kind.k, Kind.width, hRows, sharedDescriptor, TcShared.byteAddress, hByte]

/-- Every issued QK or PV has supported operand descriptors, valid addresses and an in-range D. -/
theorem actualMmaIssueShape {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {s : OperandSpec} {accum : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s accum mask) : IssueShape l i d s mask := by
  have ⟨group, hLaunch⟩ := actualMmaOwnership hX hi
  have hThread := event_thread_lt hX hi.choose_spec
  have hMask : OutputMaskValid .one (List.replicate 4 0) := by decide
  rcases actualMmaInstruction hX hi with ⟨block,frag,hQk⟩ | ⟨block,frag,hPv⟩
  · have hQ := hQk.queryOperand hp hX
    obtain ⟨use,hB⟩ := hQk.keyOperand hp hX
    have hDest := hQk.scoreDestination hp hX
    have hBound := scoreColumn_range (qkStage block)
    refine ⟨hThread, hQ.descriptor ▸ (show Valid qkDescriptor by decide), ?_, hLaunch,
      hQ.address ▸ queryEncoded hp (qkStage block) frag, hB ▸ cacheEncoded hp use frag true,
      .inl (by omega), ?_, ?_, fun op index hk => .inl (qkAddresses hQ hB op index hk)⟩
    · rwa [group, qkZeroMask hX hQk]
    · simp [hQ.shared]
    · rw [hQ.descriptor, show resultColumns qkDescriptor = 128 by decide]
      omega
  · obtain ⟨slot,hB,hDesc,_,_⟩ := hPv.valueOperand hp hX
    obtain ⟨hShared,_,hZero⟩ := hPv.fixedOperandFields hX
    have hA := hPv.probabilityAddress hp hX
    have hBnd := probabilityColumn_range (pvSite block).stage
    have hScore := scoreColumn_range (pvSite block).stage
    have hFrag := frag.isLt
    have hSmall : probabilityColumn (pvSite block).stage+8*frag.val+8 ≤ 512 := by omega
    have hDest := hPv.outputDestination hp hX
    have hBound := outputColumn_range (pvSite block).stage
    have hEncoded := hB ▸ cacheEncoded hp slot.val frag false
    refine ⟨hThread, hDesc ▸ (show Valid pvDescriptor by decide), ?_, hLaunch,
      hShared ▸ hEncoded, hEncoded, .inl (by omega), ?_, ?_, pvAddresses hDesc hB hA hSmall⟩
    · rwa [group, hZero]
    · simp [hDesc, halfDatapath, pvDescriptor]
    · rw [hDesc, show resultColumns pvDescriptor = 128 by decide]
      omega

end PTX.Kernels.TmlFa4Fwd.Thread

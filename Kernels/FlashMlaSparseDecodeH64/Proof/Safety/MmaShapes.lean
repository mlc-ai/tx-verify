-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow

@[expose] public section

/-! # Issued Tensor Core operations meet the model's shape checks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow TcMma MmaDataTrace Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g : Nat}

set_option maxRecDepth 100000

private theorem shared_limit (hpre : Pre P L mem0) : L.sharedBase + 223232 ≤ 2 ^ 18 := by
  rw [hpre.sharedBase]
  exact hpre.sharedRange

private theorem shared_align (hpre : Pre P L mem0) : L.sharedBase % 16 = 0 := by
  rw [hpre.sharedBase]
  have h := hpre.sharedAlignment
  omega

private theorem key_encoded (hpre : Pre P L mem0) (block : Nat) (k : Fin 16) :
    SharedEncoded (keyDescriptor L block k) := by
  have hShared := shared_limit hpre
  have hAlign := shared_align hpre
  have hk := k.isLt
  let start := kvBase L block + 16 * qkBDelta k.val
  change start < 2 ^ 18 ∧ 16 < 2 ^ 18 ∧ 1024 < 2 ^ 18 ∧
    start % 16 = 0 ∧ 16 % 16 = 0 ∧ 1024 % 16 = 0
  dsimp only [start, kvBase, qkBDelta]
  omega

private theorem value_encoded (hpre : Pre P L mem0) (block : Nat) (k : Fin 8) :
    SharedEncoded (valueDescriptor L block k) := by
  have hShared := shared_limit hpre
  have hAlign := shared_align hpre
  have hk := k.isLt
  let start := kvBase L block + 16 * pvBDelta k.val
  change start < 2 ^ 18 ∧ 8192 < 2 ^ 18 ∧ 1024 < 2 ^ 18 ∧
    start % 16 = 0 ∧ 8192 % 16 = 0 ∧ 1024 % 16 = 0
  dsimp only [start, kvBase, pvBDelta]
  omega

private theorem probability_encoded (hpre : Pre P L mem0) (k : Fin 8) :
    SharedEncoded (probabilityDescriptor L k) := by
  have hShared := shared_limit hpre
  have hAlign := shared_align hpre
  have hk := k.isLt
  let start := L.sharedBase + 204800 + 2048 * (k.val / 2)
  change start < 2 ^ 18 ∧ 1024 < 2 ^ 18 ∧ 128 < 2 ^ 18 ∧
    start % 16 = 0 ∧ 1024 % 16 = 0 ∧ 128 % 16 = 0
  dsimp only [start]
  omega

private theorem qk_shape (hpre : Pre P L mem0) (hg : g < L.threads) (i block : Nat)
    (k : Fin 16) : IssueShape L (g, i) tmemP (qkOperands L g block k) [0, 0, 0, 0] := by
  have hKey := key_encoded hpre block k
  refine ⟨hg, qkIdesc_valid, ?_, ?_, hKey, hKey, .inl rfl, ?_, ?_, ?_⟩
  · change OutputMaskValid .one [0, 0, 0, 0]
    decide
  · exact ⟨[ctaOf L g], mma_group_thread hpre hg, rfl, rfl⟩
  · intro _ _ hn
    cases hn
  · change tmemP % 2 ^ 16 + resultColumns qkDescriptor ≤ 512
    decide
  · intro op n hn
    cases op with
    | a =>
      norm_num [qkOperands, qkDescriptor, Operand.bytes, Operand.rows, Kind.k, Kind.width] at hn
      obtain ⟨row, k', byte, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hn
      exact .inr ⟨rfl, _, qkQueryByte L g block k row k' byte⟩
    | b =>
      norm_num [qkOperands, qkDescriptor, Operand.bytes, Operand.rows, Operand.extent,
        Kind.k, Kind.width] at hn
      obtain ⟨row, k', byte, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hn
      exact .inl ⟨_, qkKeyByte L g block k row k' byte⟩

private theorem pv_shape (hpre : Pre P L mem0) (hg : g < L.threads) (i block : Nat)
    (k : Fin 8) : IssueShape L (g, i) (pvDest k) (pvOperands L g block k) [0, 0, 0, 0] := by
  have hP := probability_encoded hpre k
  have hV := value_encoded hpre block k
  refine ⟨hg, pvIdesc_valid, ?_, ?_, hP, hV, ?_, ?_, ?_, ?_⟩
  · change OutputMaskValid .one [0, 0, 0, 0]
    decide
  · exact ⟨[ctaOf L g], mma_group_thread hpre hg, rfl, rfl⟩
  · exact .inl (by fin_cases k <;> decide)
  · intro _ hk _
    cases hk
  · change pvDest k % 2 ^ 16 + resultColumns pvDescriptor ≤ 512
    fin_cases k <;> decide
  · intro op n hn
    cases op with
    | a =>
      norm_num [pvOperands, pvDescriptor, Operand.bytes, Operand.rows, Kind.k, Kind.width] at hn
      obtain ⟨row, k', byte, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hn
      exact .inl ⟨_, pvProbabilityByte L g block k row k' byte⟩
    | b =>
      norm_num [pvOperands, pvDescriptor, Operand.bytes, Operand.rows, Operand.extent,
        Kind.k, Kind.width] at hn
      obtain ⟨row, k', byte, rfl⟩ := MmaAccessWindow.operand_slot (rows := 256) hn
      exact .inl ⟨_, pvValueByte L g block k row k' byte⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- Every actual MMA has a valid shape and an address for each operand byte. -/
theorem mma_issue_shape {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) : IssueShape L i d s mask := by
  obtain ⟨g, j⟩ := i
  have hg := Frame.lt_of_get hX hi.choose_spec
  rcases MmaAccessWindow.mma_spec hpre hX hs ht hi with ⟨rfl,
    ⟨block, k, rfl, rfl, _, _⟩ | ⟨block, k, rfl, rfl, _, _⟩⟩
  · exact qk_shape hpre hg j block k
  · exact pv_shape hpre hg j block k

/-- Every actual query copy has a supported source address for all its bytes. -/
theorem copy_issue_shape {i : EvId} {c : TcCopy.Spec} (hi : X.CpIssue i c) : CopySafe c := by
  obtain ⟨g, j⟩ := i
  obtain ⟨k, rfl⟩ := MmaAccessWindow.copy_spec hpre hX hs ht hi
  refine ⟨key_encoded hpre 0 k, ?_⟩
  intro cta hc n hn
  have hCta : cta = ctaOf L g := by simpa [queryCopySpec] using hc
  subst cta
  have h : n < 128 * 32 := hn
  obtain ⟨row, k', byte, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) h
  exact ⟨_, queryCopyByteLoc L g k row k' byte⟩

/-- Neither of the kernel's two MMA forms reuses a collector buffer. -/
theorem collector_safe : CollectorSafe X := by
  apply collectorSafe_of_noReuse
  rintro ⟨g, j⟩ d s a m hi
  rcases (MmaAccessWindow.mma_spec hpre hX hs ht hi).2 with
    ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ <;> exact ⟨rfl, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

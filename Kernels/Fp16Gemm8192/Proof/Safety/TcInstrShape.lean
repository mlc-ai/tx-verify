-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcWrites
public import Kernels.Fp16Gemm8192.Proof.Safety.MemoryPeer

@[expose] public section

/-! # The MMAs' issue shape and operands, from the interface

An MMA of the kernel is issued by warp 8 or 9 of a leader CTA, of the instruction descriptor
`InputRing.mmaDescriptor` (`kind::f16`, `cta_group::2`, M = N = 256), of the shared descriptors
of its K step's stage tiles, unmasked, at column `256 * (w % 2)` of its CTA pair
(`Safety.mma_source`): a valid shape, encoded descriptors and a CTA pair the launch places. Every
operand byte has a shared location (`OperandCopies`), and A is read from shared memory, so no
Tensor Memory A source is needed (`completed_a_sources`). The kernel issues no `tcgen05.cp`
(`copy_safe`) and its MMAs reuse no collector buffer (`collector_safe`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX PTX.Flow TcMma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel's MMA descriptor is valid. -/
theorem mmaDescriptor_valid' : Valid InputRing.mmaDescriptor := by decide

/-- A K step's shared descriptor of a stage of the input ring is encoded. -/
theorem stepDescriptor_encoded (hpre : Pre P L mem0) {s q j : Nat} (hs : s < 4) (hq : q < 3)
    (hj : j < 4) : SharedEncoded (stepDescriptor (L.sharedBase + InputRing.stageOff s q) 0 j) := by
  have hr := hpre.sharedRange
  have ha := hpre.sharedAlignment
  unfold sharedBytes at hr
  have hlt : InputRing.stageOff s q + 16384 ≤ 197632 := by
    unfold InputRing.stageOff; split_ifs <;> omega
  have hm : InputRing.stageOff s q % 16 = 0 := by unfold InputRing.stageOff; split_ifs <;> omega
  simp only [SharedEncoded, stepDescriptor]
  exact ⟨by omega, by decide, by decide, by omega, trivial, trivial⟩

/-- **An MMA's issue shape.** -/
theorem issue_shape (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hoc : OperandCopies L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) : IssueShape L i d s mask := by
  obtain ⟨hg, hlead, hw, -, hd, hm, -⟩ := mma_source hX ht hi
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hcta : i.1 / L.block < L.grid := by
    simp only [Launch.threads] at hg
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
  -- the slot and K step from the issue's thread fact
  obtain ⟨pc, he⟩ := hi
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨m, sl', j', -, -, -, hsp, -⟩ := ht.mma_issue hg he hσ rfl
  subst hd hm
  refine ⟨hg, ?_, by rw [hsp]; exact (by decide : OutputMaskValid .two (List.replicate 8 0)), ?_,
    ?_, ?_, ?_, ?_, ?_, fun op index hindex => .inl ?_⟩
  · rw [hsp]; exact mmaDescriptor_valid'
  · rw [hsp]
    refine ⟨[i.1 / L.block / 2 * 2, i.1 / L.block / 2 * 2 + 1], ?_, rfl, rfl⟩
    simp only [InputRing.mmaSpec, InputRing.mmaDescriptor]
    rw [Launch.ctaGroup_two, rankOfCta_eq hpre, peerCta_eq hpre hcta (by omega),
      peerCta_eq hpre hcta (by omega)]
    simp only [Option.bind_some]
    have h0 : i.1 / L.block % 2 / 2 * 2 = 0 := by omega
    rw [h0, Nat.add_zero, Nat.zero_add]
  · rw [hsp]
    exact stepDescriptor_encoded hpre sl'.isLt (by omega) j'.isLt
  · rw [hsp]
    exact stepDescriptor_encoded hpre sl'.isLt (by decide) j'.isLt
  · left
    omega
  · intro address ha
    rw [hsp] at ha
    cases ha
  · rw [hsp]
    simp only [InputRing.mmaSpec, InputRing.mmaDescriptor, resultColumns, CtaGroup.size, true_or,
      ↓reduceIte]
    omega
  · -- every operand byte has a shared location
    have hb : index < 8192 := by
      rw [hsp] at hindex
      cases op <;> simpa [Operand.bytes, Operand.rows, Operand.extent, InputRing.mmaSpec,
        InputRing.mmaDescriptor, Kind.k, Kind.width] using hindex
    obtain ⟨copy, o, x, y, -, hz⟩ := hoc i _ s acc _ ⟨pc, he⟩
      (match op with | .a => false | .b => true) (index / 2) (by omega)
    obtain ⟨l, hl, -⟩ := hz (index % 2) (Nat.mod_lt _ (by decide))
    rw [show 2 * (index / 2) + index % 2 = index by omega] at hl
    cases op <;> exact ⟨l, hl⟩

/-- **An MMA reads no Tensor Memory A operand**, so every such read has a source vacuously. -/
theorem completed_a_sources (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ∀ i cell, X.async.mmaDone i = true → X.MmaACell i cell →
      ∃ source value, ReadSource L X .a source i cell ∧ Wrote L Prod X source cell value := by
  rintro i cell - ⟨d, s, acc, mask, index, b, hi, hc⟩
  obtain ⟨-, -, -, ⟨sl, j, rfl⟩, -⟩ := mma_source hX ht hi
  simp [aCell, InputRing.mmaSpec] at hc

/-- **The kernel issues no `tcgen05.cp`.** -/
theorem copy_safe (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ∀ i c, X.CpIssue i c → CopySafe c := by
  intro i c ⟨pc, he⟩
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  exact absurd rfl (ht.no_tc_cp (Frame.lt_of_get hX he) he hσ)

/-- **The kernel's MMAs reuse no collector buffer.** -/
theorem collector_safe (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    CollectorSafe X :=
  collectorSafe_of_noReuse fun _ _ _ _ _ hu => by
    obtain ⟨-, -, -, ⟨sl, j, rfl⟩, -⟩ := mma_source hX ht hu
    exact ⟨rfl, rfl⟩

end PTX.Kernels.Fp16Gemm8192.Proof.Safety

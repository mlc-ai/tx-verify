-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstrValues
public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstrShape

@[expose] public section

/-! # The MMAs' numerical results, from the interface

The MMAs of a warp write one accumulator: the cells of its buffer in its CTA pair, the same for
every slot and K step (`writeCell_step`). An MMA that completed read its operands
(`TcEffectsOk`), whose elements are FP16 values (`operand_elements`), so its ideal arithmetic
succeeds on a `.f32` old value or none (`eval_ok`). An accumulating MMA follows an MMA of its
thread (`ThreadFacts.mma_acc_prev`); the latest one before it is its accumulator source
(`prev_source`): it completed first (`CompletionClosed`), it is a pipeline predecessor
(`pipeline_of`), every other write of the cell is an MMA of the same thread, ordered before the
source or after the consumer by the pipeline (`same_cell_issuer`), and the allocation's release
follows the consumer's completion (`MmaReleased`). By induction along the thread, every cell of a
completed MMA has a value (`results`): `CompletedValues`, and the accumulator clause of
`TcMma.SourceSafe` (`completed_accumulator_sources`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX PTX.Flow TcMma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The accumulators' lifetimes: every release of an allocation covering a cell of an MMA's
accumulator follows the MMA's completion. -/
def MmaReleased (L : Launch) (X : Execution) : Prop :=
  ∀ i d sp acc mask row col cell, X.MmaIssue i d sp acc mask →
    resultCell sp d row col = some cell → ∀ key r, r ∈ X.tmemHistory key →
      Tmem.Pair.Covers L X r cell.cta i cell.column → ∀ release, Tmem.Pair.ReleaseOf L X r release →
        DoneBefore L X i release

/-- The cells an MMA of a warp writes do not depend on its stage or K step. -/
theorem writeCell_step (L : Launch) (cta w sl j sl' j' d : Nat) (mask : List Nat) (row col : Nat) :
    writeCell (InputRing.mmaSpec L cta w sl j) d mask row col =
      writeCell (InputRing.mmaSpec L cta w sl' j') d mask row col := rfl

/-- An MMA's result cell has a row and a column of the 256 x 256 accumulator. -/
theorem resultCell_lt {cta w sl j d row col : Nat} {cell : Cell}
    (h : resultCell (InputRing.mmaSpec L cta w sl j) d row col = some cell) :
    row < 256 ∧ col < 256 := by
  unfold resultCell at h
  dsimp only at h
  split at h
  · rename_i hc
    exact ⟨hc.2.2.1, hc.2.2.2.1⟩
  · cases h

/-- An unmasked MMA writes each of its result cells. -/
theorem writeCell_of_resultCell {cta w sl j d row col : Nat} {cell : Cell}
    (h : resultCell (InputRing.mmaSpec L cta w sl j) d row col = some cell) :
    writeCell (InputRing.mmaSpec L cta w sl j) d (List.replicate 8 0) row col = some cell := by
  have hr := (resultCell_lt h).1
  have hl := (resultCell_bounds h).1
  have hv : OutputMaskValid (InputRing.mmaSpec L cta w sl j).descriptor.group
      (List.replicate 8 0) := by
    show OutputMaskValid .two (List.replicate 8 0)
    decide
  unfold writeCell
  simp only [hv, not_true_eq_false, ↓reduceIte, Option.bind_eq_bind, h, Option.bind_some]
  simp only [InputRing.mmaSpec, InputRing.mmaDescriptor, CtaGroup.size]
  rw [List.getElem?_replicate_of_lt (by omega)]
  simp

/-- The operand byte counts of the kernel's MMA descriptor. -/
theorem mmaDescriptor_bytes :
    (if InputRing.mmaDescriptor.ws = true ∧ InputRing.mmaDescriptor.m < 128 then 128
      else InputRing.mmaDescriptor.m) * InputRing.mmaDescriptor.kind.k *
      InputRing.mmaDescriptor.kind.width = 8192 ∧
    InputRing.mmaDescriptor.n * InputRing.mmaDescriptor.kind.k *
      InputRing.mmaDescriptor.kind.width = 8192 := by
  decide

/-- A completed MMA of the kernel read its operands, of 8192 bytes each. -/
theorem operands_of_done (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) (hd : X.async.mmaDone i = true) :
    ∃ ops, X.async.mmaOperands i = some ops ∧ ops.a.length = 8192 ∧ ops.b.length = 8192 := by
  obtain ⟨-, -, -, ⟨sl, j, hs⟩, -⟩ := mma_source hX ht hi
  have hsd : s.descriptor = InputRing.mmaDescriptor := by rw [hs]; rfl
  have hst := hX.tma.2.1.2 i hd
  obtain ⟨ops, hops⟩ : ∃ ops, X.async.mmaOperands i = some ops := by
    cases h : X.async.mmaOperands i with
    | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
    | some ops => exact ⟨ops, rfl⟩
  obtain ⟨-, ha, hb⟩ := hX.tma.2.1.mma_observation_shape hi hops
  rw [hsd] at ha hb
  exact ⟨ops, hops, ha.trans mmaDescriptor_bytes.1, hb.trans mmaDescriptor_bytes.2⟩

/-- The ideal dot product of FP16 elements is a real number. -/
theorem dot_ok {d : Descriptor} (hk : d.kind = .f16 .f16 .f32) {a b : List (Option Byte)}
    {row col : Nat} :
    ∀ n, (∀ k, k < n → ∃ x, Assumption.idealMmaElement (.f16 .f16 .f32) .a a row k = .ok x) →
      (∀ k, k < n → ∃ y, Assumption.idealMmaElement (.f16 .f16 .f32) .b b col k = .ok y) →
      ∃ r, Assumption.idealMmaDot d a b row col n = .ok r
  | 0, _, _ => ⟨0, rfl⟩
  | n + 1, ha, hb => by
    obtain ⟨r, hr⟩ := dot_ok hk n (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    obtain ⟨x, hx⟩ := ha n (by omega)
    obtain ⟨y, hy⟩ := hb n (by omega)
    exact ⟨_, by simp only [Assumption.idealMmaDot, hk, hr, hx, hy]; rfl⟩

/-- **An MMA's ideal arithmetic succeeds** on its FP16 operands and an `.f32` old value (or none,
when it does not accumulate). -/
theorem eval_ok (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hoc : OperandCopies L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (hla : ops.a.length = 8192)
    (hlb : ops.b.length = 8192) {row col : Nat} (hrow : row < 256) (hcol : col < 256)
    {old : Option Value} (hold : acc = true → ∃ r, old = some (.float .f32 r)) :
    ∃ r, eval Prod s.descriptor acc ops.a ops.b old row col = .ok (.float .f32 r) := by
  obtain ⟨-, -, -, ⟨sl, j, hs⟩, -⟩ := mma_source hX ht hi
  have hsd : s.descriptor = InputRing.mmaDescriptor := by rw [hs]; rfl
  obtain ⟨dot, hdot⟩ := dot_ok (d := InputRing.mmaDescriptor) rfl (a := ops.a) (b := ops.b) 16
    (fun k hk => by simpa using operand_elements hpre hX ht hoc hi hops false hrow hk)
    (fun k hk => by simpa using operand_elements hpre hX ht hoc hi hops true hcol hk)
  obtain ⟨prev, hprev⟩ : ∃ prev, Assumption.idealMmaAccumulator .f32 acc old = .ok prev := by
    cases acc
    · exact ⟨0, rfl⟩
    · obtain ⟨r, rfl⟩ := hold rfl
      exact ⟨r, rfl⟩
  refine ⟨dot + prev, ?_⟩
  rw [hsd]
  show Assumption.execIdealMma InputRing.mmaDescriptor acc ops.a ops.b old row col = _
  have hc : TcMma.Valid InputRing.mmaDescriptor ∧ row < InputRing.mmaDescriptor.m ∧
      col < InputRing.mmaDescriptor.n ∧
      ops.a.length = TcMma.Operand.bytes .a InputRing.mmaDescriptor ∧
      ops.b.length = TcMma.Operand.bytes .b InputRing.mmaDescriptor :=
    ⟨mmaDescriptor_valid', hrow, hcol, by rw [hla]; rfl, by rw [hlb]; rfl⟩
  have hsh : TcMma.operandRow InputRing.mmaDescriptor row col = row := rfl
  have hkind : InputRing.mmaDescriptor.kind = .f16 .f16 .f32 := rfl
  simp [Assumption.execIdealMma, hc, hsh, hkind, hprev, bind, Except.bind, pure,
    Except.pure, TcMma.Kind.k]
  rw [hdot]

/-- **The accumulator source of an accumulating MMA**: the latest MMA of its thread before it. -/
theorem prev_source (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrel : MmaReleased L X) {g k d : Nat} {s : OperandSpec}
    {mask : List Nat} {row col : Nat} {cell : Cell} (hi : X.MmaIssue (g, k) d s true mask)
    (hpos : writeCell s d mask row col = some cell) (hd : X.async.mmaDone (g, k) = true) :
    ∃ k', k' < k ∧ ∃ d' s' acc' mask', X.MmaIssue (g, k') d' s' acc' mask' ∧
      writeCell s' d' mask' row col = some cell ∧ X.async.mmaDone (g, k') = true ∧
      ReadSource L X .acc (g, k') (g, k) cell := by
  classical
  obtain ⟨pc, he⟩ := id hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨k0, pc0, d0, s0, a0, m0, hk0, he0⟩ := ht.mma_acc_prev hg he hσ rfl
  -- the latest MMA of the thread before it
  let Q : Nat → Prop := fun k' => k' < k ∧
    ∃ pc d s a m, X.get (g, k') = some ⟨pc, .tc (.mma d s a m)⟩
  have hQK : Q (Nat.findGreatest Q k) :=
    Nat.findGreatest_spec (m := k0) hk0.le ⟨hk0, pc0, d0, s0, a0, m0, he0⟩
  have hmax : ∀ k', Nat.findGreatest Q k < k' → k' ≤ k → ¬ Q k' :=
    fun k' h1 h2 => Nat.findGreatest_is_greatest h1 h2
  set K := Nat.findGreatest Q k
  obtain ⟨hK, pc', d', s', a', m', he'⟩ := hQK
  have hi' : X.MmaIssue (g, K) d' s' a' m' := ⟨pc', he'⟩
  obtain ⟨-, -, -, ⟨sl, j, rfl⟩, rfl, rfl, -⟩ := mma_source hX ht hi
  obtain ⟨-, -, -, ⟨sl', j', rfl⟩, rfl, rfl, -⟩ := mma_source hX ht hi'
  have hpos' : writeCell (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) sl' j')
      (256 * (g % L.block / 32 % 2)) (List.replicate 8 0) row col = some cell := by
    rw [writeCell_step L _ _ sl' j' sl j]; exact hpos
  have hc := writeCell_resultCell hpos
  have hc' := writeCell_resultCell hpos'
  have hdone : X.async.mmaDone (g, K) = true :=
    hX.mmaCompletion (g, K) (g, k) ⟨rfl, hK, pipeline_of hpre hX ht hi' hi hc' hc hK,
      _, _, a', _, _, _, true, _, hi', hi, fun r c => rfl, row, col, cell, hpos'⟩ hd
  refine ⟨K, hK, _, _, a', _, hi', hpos', hdone, fun h => by
    have := congrArg Prod.snd h; simp only at this; omega,
    .inl ⟨_, _, _, _, row, col, hi', hpos'⟩, .inl (.inr (pipeline_of hpre hX ht hi' hi hc' hc hK)),
    fun other hw => ?_, fun key r hr hcov release hrl =>
      .inl (.of_mma hi <| hrel _ _ _ _ _ _ _ _ hi hc key r hr
      hcov release hrl)⟩
  -- every other write of the cell: an MMA of the thread, before the source or after the consumer
  obtain ⟨d2, s2, a2, m2, r2, c2, hi2, hc2⟩ := write_mma hX ht hw
  obtain ⟨og, ok⟩ := other
  have hsame := (same_cell_issuer hpre hX ht hi2 hi hc2 hc).1
  simp only at hsame
  subst hsame
  rcases Nat.lt_trichotomy ok K with h | rfl | h
  · exact .inr (.inl (.inl (.inr (pipeline_of hpre hX ht hi2 hi' hc2 hc' h))))
  · exact .inl rfl
  · rcases Nat.lt_trichotomy ok k with h2 | rfl | h2
    · obtain ⟨pc2, he2⟩ := hi2
      exact absurd ⟨h2, pc2, _, _, _, _, he2⟩ (hmax ok h h2.le)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr (.inr (pipeline_of hpre hX ht hi hi2 hc hc2 h2))))

/-- **Every cell of a completed MMA has a value**: the ideal result of its operands and of its
accumulator source's value. -/
theorem results (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hoc : OperandCopies L X) (hrel : MmaReleased L X) :
    ∀ k g d s acc mask row col cell, X.MmaIssue (g, k) d s acc mask →
      writeCell s d mask row col = some cell → X.async.mmaDone (g, k) = true →
      ∃ r, Result L Prod X (g, k) cell (.float .f32 r) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g d s acc mask row col cell hi hpos hd
  obtain ⟨ops, hops, hla, hlb⟩ := operands_of_done hX ht hi hd
  have hrc : row < 256 ∧ col < 256 := by
    obtain ⟨-, -, -, ⟨sl, j, rfl⟩, -⟩ := mma_source hX ht hi
    exact resultCell_lt (writeCell_resultCell hpos)
  cases acc
  · obtain ⟨r, hr⟩ := eval_ok hpre hX ht hoc hi hops hla hlb hrc.1 hrc.2 (old := none)
      (fun h => by cases h)
    exact ⟨r, .overwrite hi hpos hops hr⟩
  · obtain ⟨k', hk', d', s', a', m', hi', hpos', hd', hsrc⟩ :=
      prev_source hpre hX ht hrel hi hpos hd
    obtain ⟨r', hr'⟩ := ih k' hk' g d' s' a' m' row col cell hi' hpos' hd'
    obtain ⟨r, hr⟩ := eval_ok hpre hX ht hoc hi hops hla hlb hrc.1 hrc.2
      (old := some (.float .f32 r')) (fun _ => ⟨r', rfl⟩)
    exact ⟨r, .accumulate hi hpos hops hr' hsrc hr⟩

/-- **A completed MMA's cells have values.** -/
theorem completed_values (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hoc : OperandCopies L X) (hrel : MmaReleased L X) (i : EvId) :
    CompletedValues L Prod X i := by
  intro hd cell ⟨d, s, acc, mask, row, col, hi, hpos⟩
  obtain ⟨r, h⟩ := results hpre hX ht hoc hrel i.2 i.1 d s acc mask row col cell hi hpos hd
  exact ⟨_, h⟩

/-- **A completed accumulating MMA's old values have sources.** -/
theorem completed_accumulator_sources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hoc : OperandCopies L X) (hrel : MmaReleased L X) :
    ∀ i cell, X.async.mmaDone i = true → X.MmaReadCell i cell →
      ∃ source value, ReadSource L X .acc source i cell ∧ Wrote L Prod X source cell value := by
  intro i cell hd ⟨d, s, mask, row, col, hi, hc⟩
  obtain ⟨-, -, -, ⟨sl, j, rfl⟩, rfl, rfl, -⟩ := mma_source hX ht hi
  have hpos := writeCell_of_resultCell hc
  obtain ⟨k', -, d', s', a', m', hi', hpos', hd', hsrc⟩ := prev_source hpre hX ht hrel hi hpos hd
  obtain ⟨r, hr⟩ := results hpre hX ht hoc hrel k' i.1 d' s' a' m' row col cell hi' hpos' hd'
  exact ⟨_, _, hsrc, .inl hr⟩

end PTX.Kernels.Fp16Gemm8192.Proof.Safety

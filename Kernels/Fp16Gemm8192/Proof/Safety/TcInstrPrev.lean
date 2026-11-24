-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstrResult

@[expose] public section

/-! # The accumulator source of every cell of an accumulating MMA

The latest MMA of an accumulating MMA's thread before it is the accumulator source of every cell
the MMA writes (`mmaAccSources`): as for one cell (`prev_source`), the same latest MMA serves every
cell, and no MMA of the thread lies between the two. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX PTX.Flow TcMma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel's MMAs write the cell of row and column 0. -/
theorem resultCell_zero (L : Launch) (cta w s j : Nat) :
    ∃ cell, resultCell (InputRing.mmaSpec L cta w s j) (256 * (w % 2)) 0 0 = some cell := by
  have hw : w % 2 < 2 := Nat.mod_lt _ (by decide)
  have hv : Valid InputRing.mmaDescriptor := by decide
  have h1 : 256 * (w % 2) / 2 ^ 16 = 0 := by omega
  have h2 : 256 * (w % 2) % 2 ^ 16 = 256 * (w % 2) := by omega
  unfold resultCell
  simp only [InputRing.mmaSpec, h1, h2, CtaGroup.size, LaneAligned, resultColumns,
    InputRing.mmaDescriptor] at hv ⊢
  have h3 : 256 * (w % 2) + 256 ≤ 512 := by omega
  simp [hv, h3]

/-- **The accumulator sources** (`MmaAccSources`). -/
theorem mmaAccSources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrel : MmaReleased L X) : MmaAccSources L X := by
  classical
  intro g k d s mask hi hd
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
  -- the latest MMA has completed: it shares the first cell with the MMA
  have hpos0 : writeCell (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) sl' j')
      (256 * (g % L.block / 32 % 2)) (List.replicate 8 0) 0 0 =
      writeCell (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) sl j)
      (256 * (g % L.block / 32 % 2)) (List.replicate 8 0) 0 0 :=
        writeCell_step L _ _ sl' j' sl j _ _ _ _
  obtain ⟨cell0, hc0⟩ : ∃ cell0,
    writeCell (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) sl j)
      (256 * (g % L.block / 32 % 2)) (List.replicate 8 0) 0 0 = some cell0 :=
    let ⟨c0, h0⟩ := resultCell_zero L (g / L.block) (g % L.block / 32) sl j
    ⟨c0, writeCell_of_resultCell h0⟩
  have hc0' : writeCell (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) sl' j')
      (256 * (g % L.block / 32 % 2)) (List.replicate 8 0) 0 0 = some cell0 := by
    rw [hpos0]; exact hc0
  have hdone : X.async.mmaDone (g, K) = true :=
    hX.mmaCompletion (g, K) (g, k) ⟨rfl, hK,
      pipeline_of hpre hX ht hi' hi (writeCell_resultCell hc0') (writeCell_resultCell hc0) hK,
      _, _, a', _, _, _, true, _, hi', hi, fun r c => rfl, 0, 0, cell0, hc0'⟩ hd
  refine ⟨K, hK, ⟨_, _, _, _, hi'⟩, hdone, fun i pci dst sp acc mask h1 h2 hget =>
    hmax i h1 h2.le ⟨h2, pci, dst, sp, acc, mask, hget⟩, fun row col cell hpos => ?_⟩
  have hpos' : writeCell (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) sl' j')
      (256 * (g % L.block / 32 % 2)) (List.replicate 8 0) row col = some cell := by
    rw [writeCell_step L _ _ sl' j' sl j]; exact hpos
  have hc := writeCell_resultCell hpos
  have hc' := writeCell_resultCell hpos'
  refine ⟨fun h => by
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

end PTX.Kernels.Fp16Gemm8192.Proof.Safety

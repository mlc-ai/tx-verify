-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Safety.Objects

@[expose] public section

/-! # The Tensor Memory load, access and MMA instruction branches of `Unsafe`

Every loaded word has the MMA as its source (`sourceSafe`, `ld_source`). Every Tensor Memory
access is allocated and completes before the release (`no_accessUnsafe`, `access_allocated`,
`dealloc_done`). The MMA has a valid issue shape (`mma_issueShape`) and its completed cells hold
its products (`no_instructionUnsafe`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow Tmem.Pair
noncomputable section
variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

/-- **Every Tensor Memory read has a source**: every loaded word the MMA's result, and the MMA
reads neither its accumulator nor an A operand in Tensor Memory. -/
theorem sourceSafe : TcMma.SourceSafe L [] X := by
  refine TcMma.sourceSafe_iff.mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨g, i⟩ j cell ⟨ta, vs, sh, ⟨pc, hl⟩, hj, rfl⟩
    have hl0 := hl
    obtain rfl := hW.tld_shape hl
    obtain ⟨hg, hi, rfl, rfl, rfl⟩ := hW.tld hl
    obtain ⟨⟨ta', vs', sh', ⟨pc', hl'⟩, -, hcell⟩, hs, hv⟩ :=
      ld_source hpre hX hW hg hi (by rw [hW.vals] at hj; exact hj)
    rw [hl0] at hl'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hl'
    obtain ⟨-, rfl, rfl, rfl⟩ := hl'
    rw [← hcell]
    exact ⟨_, _, hs, hv⟩
  · rintro ⟨g, j⟩ cell - ⟨d, s, mask, row, col, ⟨pc, hm⟩, _⟩
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hW.mma hm
    cases h
  · rintro ⟨g, j⟩ cell - ⟨d, s, acc, mask, index, b, ⟨pc, hm⟩, ha⟩
    obtain ⟨-, -, -, -, -, rfl, -, -⟩ := hW.mma hm
    simp [TcMma.aCell, mmaSpec] at ha

/-- The kernel MMA's shape, masks, CTA, descriptors, D range and every operand address. -/
theorem mma_issueShape (hm : hd 0 + 2 + (P 0).n0 < m 0) :
    TcMma.IssueShape L (0, hd 0 + 2 + (P 0).n0) (P 0).c (mmaSpec L.sharedBase) mmaMask := by
  have hT := threads_eq hpre
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  have hcs := clusterSize_eq hpre
  have hc0 := c_eq hpre hX hW (g := 0) (by decide) (by omega)
  have hcol := col_ok hpre hX hW (P := P) (m := m) (by omega)
  refine ⟨by simp [hT], show TcMma.Valid mmaDesc by decide,
    show TcMma.OutputMaskValid .one mmaMask by decide, ?_, ?_, ?_, .inl (by omega),
    fun _ h => by simp [mmaSpec] at h, ?_, ?_⟩
  · have hr := Launch.oneDim_rankOfCta hpre.oneDimLaunch.1 0
    have hsz := Launch.oneDim_clusterSizeOf hpre.oneDimLaunch.1 0
    have hco := Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1 0
    have hcg : L.ctaGroup 0 .one = some [0] := by
      simp [Launch.ctaGroup_one, Launch.peerCta, Launch.clusterStart, hcs, hr, hsz, hco,
        hpre.grid]
    simp [TcMma.OperandSpec.MatchesLaunch, mmaSpec, mmaDesc, hcg]
  · simp only [TcMma.SharedEncoded, mmaSpec, descA, Nat.reducePow]
    refine ⟨?_, by decide, by decide, ?_, by decide, by decide⟩ <;> omega
  · simp only [TcMma.SharedEncoded, mmaSpec, descB, Nat.reducePow]
    refine ⟨?_, by decide, by decide, ?_, by decide, by decide⟩ <;> omega
  · simp only [TcMma.resultColumns, mmaSpec, mmaDesc, CtaGroup.size]; simp; omega
  · intro op index hi
    cases op
    · simp only [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent,
        mmaSpec, mmaDesc,
        TcMma.Kind.k, TcMma.Kind.width, Bool.false_eq_true, and_false, false_and,
        ↓reduceIte] at hi
      rw [mmaSpec_a, ite_eq_left (by omega)]
      exact .inl ⟨_, rfl⟩
    · simp only [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent,
        mmaSpec, mmaDesc,
        TcMma.Kind.k, TcMma.Kind.width, Bool.false_eq_true, and_false, false_and, reduceCtorEq,
        ↓reduceIte] at hi
      rw [mmaSpec_b, ite_eq_left (by omega)]
      exact .inl ⟨_, rfl⟩

theorem no_instructionUnsafe : ¬ TcMma.InstructionUnsafe L [] X := by
  intro hu
  apply hu
  refine ⟨?_, fun ⟨_, _⟩ _ ⟨_, hc⟩ => (hW.no_cp hc).elim,
    TcMma.collectorSafe_of_noReuse fun ⟨_, _⟩ _ _ _ _ ⟨_, hi⟩ => ?_⟩
  swap
  · obtain ⟨-, -, -, -, -, rfl, -, -⟩ := hW.mma hi
    exact ⟨rfl, rfl⟩
  rintro ⟨g, j⟩ d s accum mask ⟨pc, hi⟩
  obtain ⟨-, hj, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hW.mma hi
  have hc0 := c_eq hpre hX hW (g := 0) (by decide) (by omega)
  have hcol := col_ok hpre hX hW (P := P) (m := m) (by omega)
  refine ⟨mma_issueShape hpre hX hW hj, ?_⟩
  intro hdone cell ⟨d', s', accum', mask', row, col, hi', hw⟩
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hW.mmaIssue hi'
  obtain ⟨rfl, hr, hc, hb⟩ := mma_writeCell_inv hw
  exact ⟨_, mma_result hpre hX hW hj (hX.tma.2.1.2 _ hdone) hr hc hb⟩

theorem no_accessUnsafe : ¬ Tmem.Pair.AccessUnsafe L X := fun hu =>
  hu fun e cell hacc => ⟨access_allocated hpre hX hW hacc, fun key r hr _ d hrel => by
    obtain ⟨t, n, pc, grp, hget⟩ := release_event hrel
    exact .inl (dealloc_done hpre hX hW d pc grp none t n e cell hget hacc)⟩

end
end PTX.Kernels.TcGemm.Proof

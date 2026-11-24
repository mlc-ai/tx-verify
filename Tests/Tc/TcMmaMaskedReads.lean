-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaRead
public import Lemmas.Tmem.TmemRun
public import Lemmas.Tcgen05.TcMmaOperands

namespace PTX.Tests.TcMmaMaskedReads
open TcMma
noncomputable section

private def L : Launch :=
  { grid := 2, block := 32, clusterSize := 2, params := fun _ => none }
private def smem : TcShared.Descriptor := ⟨0, 0, 1024, 0, false, false, .b128⟩
private def spec : OperandSpec :=
  ⟨⟨.two, .f16 .f16 .f32, 256, 256, false, false, false, false, false⟩, smem, smem, 0, 1, none, {}⟩
private def masks : List Nat := List.replicate 8 (2^32 - 1)
private def X (accumulate : Bool) : Execution := {
  tr := fun _ => [⟨0, .tc (.mma 0 spec accumulate masks)⟩],
  rf := fun _ _ => none }

-- The selected output lane is masked, but enable-input-D still permits its C read.
example : writeCell spec 0 masks 0 0 = none := rfl
private theorem old_read : (X true).MmaReadCell (0, 0) ⟨0, 0, 0⟩ :=
  ⟨0, spec, masks, 0, 0, ⟨0, rfl⟩, rfl⟩
example : (X true).MmaAccess (0, 0) ⟨0, 0, 0⟩ := .inr (.inl old_read)

-- With accumulation disabled there is no C read, independently of output masking.
example (cell : Cell) : ¬ (X false).MmaReadCell (0, 0) cell := by
  rintro ⟨d, s, mask, row, col, ⟨pc, hi⟩, _⟩
  cases hi

-- All outputs masked does not license reads from unallocated TMEM.
example : Tmem.Pair.AccessUnsafe L (X true) := by
  apply Tmem.Pair.accessUnsafe_of_unallocated (.inl (.inr (.inl old_read)))
  rintro ⟨key, pair, hp, _⟩
  cases hp

-- A masked read remains subject to either side's first release attempt.
example (Y : Execution) (h : Tmem.Pair.AccessSafe L Y) (i : EvId) (cell : Cell)
    (hi : Y.MmaReadCell i cell) (cta : Nat) (r : Tmem.Pair.Requests)
    (hr : r ∈ Y.tmemHistory cta) (hc : Tmem.Pair.Covers L Y r cell.cta i cell.column)
    (d : EvId) (hd : Tmem.Pair.ReleaseOf L Y r d)
    (hn : ¬ Tmem.Pair.FreshAfter L Y d i cell.cta cell.column) : TcMma.CompletedBefore L Y i d :=
  before_release h (.inl (.inr (.inl hi))) hr hc hd hn

-- A distinct unordered writer conflicts with this read despite the output mask.
example (Y : Execution) (reader writer : EvId) (cell : Cell)
    (hr : Y.MmaReadCell reader cell) (hw : Y.MmaCell writer cell)
    (hne : reader ≠ writer) (hwr : ¬ WriteBefore L Y writer reader)
    (hrw : ¬ ReadBefore L Y .acc reader writer) : ReadsUnsafe L Y := by
  intro h
  rcases h .acc reader writer cell hr (.inl hw) with he | he | he
  · exact hne he
  · exact hwr he
  · exact hrw he

-- Completed enabled C reads require a source, even if no output is written or loaded.
example (Y : Execution) (A : List Assumption) (i : EvId) (cell : Cell)
    (hd : Y.async.mmaDone i = true) (hr : Y.MmaReadCell i cell)
    (hn : ∀ first d s mask, ¬ Y.MmaIssue first d s false mask)
    (hs : ∀ e a vals sh, ¬ Y.TSt e a vals sh) (hc : ∀ e c, ¬ Y.CpIssue e c)
    (hsh : ∀ e s, ¬ Y.ShiftIssue e s) :
    ¬ SourceSafe L A Y := by
  intro h
  obtain ⟨source, old, -, hv⟩ := h .acc i cell ⟨hd, hr⟩
  rcases hv with hv | ⟨a, vals, sh, j, ht, -⟩ | ⟨c, k, cta, ops, row, col, lane, hcp, -⟩ |
    ⟨src, from', ⟨⟨s, hsi, -⟩, -⟩, -⟩
  · obtain ⟨first, (⟨d, s, mask, hi, _⟩ | ⟨v, a, vals, sh, j, ht, -⟩)⟩ := hv.has_initializer
    · exact hn first d s mask hi
    · exact hs _ _ _ _ ht
  · exact hs _ _ _ _ ht
  · exact hc _ _ hcp
  · exact hsh _ s hsi

end
end PTX.Tests.TcMmaMaskedReads

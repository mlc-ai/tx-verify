-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSource
public import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX Correction Epilogue

private theorem elementAddr {l : Launch} {loc : Loc} {g x y : Nat} {stage : Fin 2}
    {subbox : Fin 4} (h : (outputElementAccess l g stage subbox x y).Covers loc) :
    ∃ k < 4, loc.addr = l.sharedBase + 3072 + 65536 * stage.val + 16384 * subbox.val +
      128 * y + 16 * (x / 4 ^^^ (y % 8)) + 4 * (x % 4) + k := by
  have hLo := h.2.2.1
  have hHi := h.2.2.2
  simp only [outputElementAccess, outputChunkLoc, sharedSlot, Loc.at] at hLo hHi
  let base := l.sharedBase + 3072 + 65536 * stage.val + 16384 * subbox.val +
    128 * y + 16 * (x / 4 ^^^ (y % 8)) + 4 * (x % 4)
  exact ⟨loc.addr - base, by dsimp [base]; omega, by dsimp [base]; omega⟩

/-- Each staged element occupies bytes entirely within its output stage. -/
theorem elementStageRange {l : Launch} {loc : Loc} {g x y : Nat} {stage : Fin 2}
    {box : Fin 4} (hx : x < 32) (hy : y < 128)
    (hCover : (outputElementAccess l g stage box x y).Covers loc) :
    l.sharedBase + 3072 + 65536 * stage.val ≤ loc.addr ∧
      loc.addr < l.sharedBase + 3072 + 65536 * (stage.val + 1) := by
  obtain ⟨k, hk, hAddr⟩ := elementAddr hCover
  have hb := box.isLt
  have hSw : x / 4 ^^^ (y % 8) < 8 :=
    Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
  omega

/-- Normalized correction elements can cover the same physical byte only with the same CTA,
stage, box, row, and column. The swizzle permutes chunks within each row. -/
theorem sameNormalizedElementOfCover {l : Launch} {loc : Loc} {g g' x x' y y' : Nat}
    {stage stage' : Fin 2} {subbox subbox' : Fin 4}
    (hx : x < 32) (hx' : x' < 32) (hy : y < 128) (hy' : y' < 128)
    (h : (outputElementAccess l g stage subbox x y).Covers loc)
    (h' : (outputElementAccess l g' stage' subbox' x' y').Covers loc) :
    g / l.block = g' / l.block ∧ stage = stage' ∧ subbox = subbox' ∧ y = y' ∧ x = x' := by
  obtain ⟨k, hk, hAddr⟩ := elementAddr h
  obtain ⟨k', hk', hAddr'⟩ := elementAddr h'
  have hS := stage.isLt
  have hS' := stage'.isLt
  have hB := subbox.isLt
  have hB' := subbox'.isLt
  have hSw : x / 4 ^^^ (y % 8) < 8 :=
    Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
  have hSw' : x' / 4 ^^^ (y' % 8) < 8 :=
    Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
  have hStage : stage.val = stage'.val := by omega
  have hBox : subbox.val = subbox'.val := by omega
  have hRow : y = y' := by omega
  have hMod : x % 4 = x' % 4 := by omega
  have hSwEq : x / 4 ^^^ (y % 8) = x' / 4 ^^^ (y' % 8) := by omega
  have hDiv : x / 4 = x' / 4 := by
    rw [← hRow] at hSwEq
    simpa [Nat.xor_assoc] using congrArg (fun n => n ^^^ (y % 8)) hSwEq
  have hCta : g / l.block = g' / l.block := h.2.1.symm.trans h'.2.1
  exact ⟨hCta, Fin.ext hStage, Fin.ext hBox, hRow, by omega⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Output

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderShiftPrelude
public import Kernels.TmlFa4Fwd.Flow.Code.Part007
public import Kernels.TmlFa4Fwd.Flow.Code.Part008
public import Lemmas.Flow.Local

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- The priming iteration forms its page-table index with the decoded fixed divisor of
16. It skips the global page word exactly when the corresponding row is out of range. -/
theorem primingScratchIndex {l : Launch} {g base length : Nat} (entry : Fin 2)
    (hRow : base + 64 * entry.val < 2 ^ 31) (hLength : length < 2 ^ 31) :
    let row := base + 64 * entry.val
    Seg kernel [] l g 12 488
      [(7172, b32 entry.val), (1095, b32 base), (7302, b64 1), (1093, b32 1), (1094, b32 3),
       (1086, b32 length), (772, .pred (entry.val == 0))]
      500 [(1096, b32 row), (1097, b32 (row / 16)), (122, .pred (decide (length ≤ row))),
        (7173, b32 0), (4, .pred (entry.val == 0))] := by
  dsimp only
  let row := base + 64 * entry.val
  have hRow31 : row < 2 ^ 31 := hRow
  have hBase : base < 2 ^ 32 := by omega
  have hRow32 : row < 2 ^ 32 := by omega
  have hRow64 : row < 2 ^ 64 := by omega
  have hHalf : row / 2 < 2 ^ 32 := by omega
  have hPage : row / 16 < 2 ^ 32 := by omega
  have hLength32 : length < 2 ^ 32 := by omega
  have hEntry32 : entry.val < 2 ^ 32 := by omega
  have hEntry64 : entry.val < 2 ^ 64 := by omega
  have hOff : 64 * entry.val < 2 ^ 32 := by omega
  have hHigh : row / 4294967296 = 0 := by omega
  have hPageShift : row / 2 / 8 = row / 16 := by omega
  let regs := [(4, .pred (entry.val == 0)), (1093, b32 1), (1094, b32 3), (1086, b32 length),
    (1096, b32 row)]
  have prep : Seg kernel [] l g 5 488
      [(7172, b32 entry.val), (1095, b32 base), (7302, b64 1), (1093, b32 1), (1094, b32 3),
       (1086, b32 length), (772, .pred (entry.val == 0))] 493
      ((7529, b64 row) :: regs) := by
    intro t ht
    dsimp only [regs]
    seg_fp ht using norm_bits [row, Nat.add_comm, Nat.mod_eq_of_lt hBase,
      Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64, Nat.mod_eq_of_lt hOff,
      Nat.mod_eq_of_lt hEntry32, Nat.mod_eq_of_lt hEntry64]
  have unpack : Seg kernel [] l g 1 493 ((7529, b64 row) :: regs) 494
      ((1841, b32 0) :: regs) := by
    intro t ht
    let u := next (setReg t 1841 (b32 0))
    have hr : run kernel [] l g 1 t = some u := by
      apply run_local Flow.code_493 rfl ht
      rw [execLocalA_nil, execLocal_move rfl]
      simp [execMove, readReg, readValue, ht.2.2.2.2.1, DType.width,
        Value.bytes, b64, splitValue, toNat_ofNat_lt hRow64, hHigh, setDst, b32,
        bind, Except.bind, pure, Except.pure, u]
      rfl
    have hc : At t 493 regs := ht.mono ht.2.2.2.2.2
    exact ⟨u, hr, hc.set (by simp [regs])⟩
  have page : Seg kernel [] l g 6 494 ((1841, b32 0) :: regs) 500
      [(1096, b32 row), (1097, b32 (row / 16)), (122, .pred (decide (length ≤ row))),
        (7173, b32 0), (4, .pred (entry.val == 0))] := by
    intro t ht
    dsimp only [regs] at ht
    seg_fp ht using first
      | rfl
      | norm_bits [hPageShift, Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64,
          Nat.mod_eq_of_lt hHalf, Nat.mod_eq_of_lt hPage]
      | simp only [truncBits_ofNat hRow32 (by decide),
          truncBits_ofNat hLength32 (by decide),
          compare, Option.getD_some, signedWord hRow31, signedWord hLength,
          ge_iff_le, Int.ofNat_le]
  exact prep.comp (unpack.comp page)

set_option maxRecDepth 3000 in
theorem primingScratchBackedgeCore {l : Launch} {g : Nat} (entry : Fin 2)
    {t : TState} (ht : At t 512 [(4, .pred (entry.val == 0))]) :
    ∃ u, run kernel [] l g 3 t = some u ∧
      At u (if entry.val == 0 then 488 else 515) [(7172, b32 1), (772, .pred false)] := by
  let pick := entry.val == 0
  have hSetup : Seg kernel [] l g 2 512 [(4, .pred pick)] 514
      [(4, .pred pick), (7172, b32 1), (772, .pred false)] := by
    intro z hz
    seg_fp hz using decide
  obtain ⟨s, hs, hS⟩ := hSetup t ht
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_514 pick hS hS.2.2.2.2.1 (by simp)
  exact ⟨u, run_comp hs hu, hU.mono hU.2.2.2.2.2⟩

set_option maxRecDepth 3000 in
/-- The global read is guarded by the actual page row bound. Skipping it retains the
zero initialized by the preceding move, which the scratch store can still write. -/
theorem primingScratchPageGuard {l : Launch} {g row length : Nat} {F : List (Nat × Value)}
    {t : TState} (ht : At t 500 ((122, .pred (decide (length ≤ row))) :: F)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (if row < length then 501 else 504) F := by
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_500 (decide (length ≤ row)) ht ht.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have he : (if length ≤ row then 504 else 500 + 1) =
      (if row < length then 501 else 504) := by
    by_cases h : row < length
    · simp [h, Nat.not_le_of_gt h]
    · simp [h, Nat.le_of_not_gt h]
  simp only [decide_eq_true_eq, he] at hU
  exact ⟨u, huA, hU.mono hU.2.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

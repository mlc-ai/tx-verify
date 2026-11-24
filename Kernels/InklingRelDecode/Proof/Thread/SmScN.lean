-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScM

@[expose] public section

/-! # The 32 groups of the mask (pcs 1628-1759), composed

The values of the group `i`'s operands in the state with `i` groups done, and the state after it,
as lemmas for every `i < 32`; then the group (`seg_maskG`) at every index, and the 32 groups in a
row. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

theorem msk_po (i : Nat) : msk i (po i) = false := by
  unfold po msk
  split_ifs <;> simp_all

theorem msk_po_succ (i : Nat) : msk (i + 1) (po i) = true := by
  unfold po msk
  split_ifs <;> simp_all

theorem msk_succ_ne {i q : Nat} (hq : q ≠ po i) : msk (i + 1) q = msk i q := by
  unfold po at hq
  unfold msk
  split_ifs at hq ⊢ <;> simp_all <;> omega

theorem valuesZ_none_pair (d : D) {q : Nat} (hq : q < 32) :
    (valuesZ L g d).lookup (2447 + q) = none := by
  apply lookup_none_of_not_mem
  intro hm
  simp only [valuesZ, List.map_append, List.map_map, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range,
    Function.comp_apply] at hm
  rcases hm with ⟨k, hk, hkk⟩ | hm | ⟨k, hk, hkk⟩ | ⟨k, hk, hkk⟩ | ⟨k, hk, hkk⟩ | ⟨k, hk, hkk⟩ <;>
    omega

theorem valueZ_pair (d : D) {q : Nat} (hq : q < 32) :
    valueZ L g d (2447 + q) = valueOf L g d (2447 + q) := by
  unfold valueZ
  rw [valuesZ_none_pair d hq]
  rfl

theorem valueZ_pred_hi (d : D) {i : Nat} (h2 : 2 ≤ i) (h32 : i < 32) :
    valueZ L g d (161 - 2 * i) = .pred (visK d.e (g % L.block) d.n (2 * i + 1)) := by
  unfold valueZ valuesZ
  rw [lookup_append', lookup_range_map 98 _ 60 (161 - 2 * i), if_pos (by omega)]
  simp only [Option.some_or, Option.getD_some]
  have : colOfP (161 - 2 * i - 98) = 2 * i + 1 := by
    unfold colOfP
    split_ifs <;> omega
  rw [this]

theorem valueZ_pred_lo (d : D) {i : Nat} (h2 : 2 ≤ i) (h32 : i < 32) :
    valueZ L g d (160 - 2 * i) = .pred (visK d.e (g % L.block) d.n (2 * i)) := by
  unfold valueZ valuesZ
  rw [lookup_append', lookup_range_map 98 _ 60 (160 - 2 * i), if_pos (by omega)]
  simp only [Option.some_or, Option.getD_some]
  have : colOfP (160 - 2 * i - 98) = 2 * i := by
    unfold colOfP
    split_ifs <;> omega
  rw [this]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm

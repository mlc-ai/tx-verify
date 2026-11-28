-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumFrame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumMask

@[expose] public section

/-! # The first link of the chain: the block's reads and the mask

At the first facts of the block (`s_vm`) the registers hold the block's reads: the mask word, the
high score words and the carried statistics and the scale. The mask chain (`m_vm`) turns them into
the masked words (`w0m_facts4`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

variable (x : BitVec 64) (m l mx sk : Value) (lo hi : List Value) (mw : Value)

theorem w0c_vm_mw : lookupD (s_vm x m l mx sk lo hi mw) 1002 = mw := by
  unfold s_vm
  refine lk_snoc_head (by
    simp only [f_sldw, f_sld1F, f_car, factsFrom, hiRegs, loRegs, List.map_append, List.map_cons,
      List.map_nil, List.map_map, Function.comp_def]
    decide) (by simp)

/-- The statistics and the scale at the first facts. -/
theorem w0c_vm_car (r : Nat) (hr : r ∈ [467, 3243, 2950, 2955, 2885, 2880]) :
    lookupD (s_vm x m l mx sk lo hi mw) r = lookupD (f_car x m l mx sk) r := by
  unfold s_vm
  rw [lk_snoc (by
    simp only [List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil]
    revert hr; revert r; decide)]
  unfold f_sldw f_sld1F
  rw [lk_skip (by
    simp only [factsFrom, loRegs, List.map_map, Function.comp_def]
    revert hr; revert r; decide)]
  exact lk_head_mem (by simp only [f_car, List.map_cons, List.map_nil]; revert hr; revert r; decide)

theorem w0c_vm_hi (hlen : hi.length = 32) (c : Nat) (hc : c < 32) :
    lookupD (s_vm x m l mx sk lo hi mw) (2918 + c) = hi.getD c (.pred false) := by
  have hr : 2918 + c ∈ hiRegs := by
    simp only [hiRegs, List.mem_range'_1]; omega
  unfold s_vm
  rw [lk_snoc (by
    simp only [List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    omega)]
  unfold f_sldw f_sld1F
  rw [lk_skip (by
    simp only [factsFrom, loRegs, List.map_map, Function.comp_def, List.mem_map, List.mem_range'_1]
    rintro ⟨a, ⟨h1, h2⟩, h3⟩
    omega)]
  rw [lk_skip (by
    simp only [f_car, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    omega)]
  have hrr : hiRegs = List.range' 2918 hi.length := by simp [hiRegs, hlen]
  have hz : (hiRegs.zip hi).lookup (2918 + c) = some (hi[c]'(by omega)) := by
    rw [hrr]; exact lookup_range_zip 2918 hi c (by omega)
  unfold lookupD
  rw [lookup_factsFrom_mem hr]
  simp only [hz, Option.getD_some]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show c < hi.length by omega)]

/-- **The masked words** (`m_vm`): column `c`'s register holds the high word if the mask selects it,
else the pattern of `-inf`. -/
theorem w0c_mask {n : Nat} (hn : n < 2 ^ 32) (hmw : mw = .bits 32 (BitVec.ofNat 64 n))
    (hlen : hi.length = 32) (hb4 : ∀ c < 32, (hi.getD c (.pred false)).bytes = 4) (c : Nat)
    (hc : c < 32) :
    lookupD (m_vm x m l mx sk lo hi mw) (w0mReg c) =
      if n.testBit c = true then hi.getD c (.pred false) else w0NegInf := by
  have hk : w0mReg c ∈ (mask_facts4 (lookupD (s_vm x m l mx sk lo hi mw))).map Prod.fst := by
    simp only [mask_facts4, List.map_cons, List.map_nil]
    revert c; decide
  unfold m_vm
  rw [lk_head_mem hk]
  rw [w0m_facts4 (lookupD (s_vm x m l mx sk lo hi mw)) n hn (by rw [w0c_vm_mw, hmw])
    (fun i hi' => by rw [w0c_vm_hi x m l mx sk lo hi mw hlen i hi']; exact hb4 i hi') c hc]
  rw [w0c_vm_hi x m l mx sk lo hi mw hlen c hc]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

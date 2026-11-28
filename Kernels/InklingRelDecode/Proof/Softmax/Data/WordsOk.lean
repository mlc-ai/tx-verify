-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsTab
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The checks of the bias words' moves

One Boolean check of the moves of a path (`wOk`), and of the instructions (`wOkC`), each over the
positions of the code up to the loop's loads. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section

/-- The checks of the move at a position, the same for every path. -/
def wOkC (pc : Nat) : Bool :=
  match wSpec pc with
  | none => true
  | some sp => intPc pc && sp.item.codeB kernel pc && (pc == 1122 || wPost (pc + 1) == wPost pc)

/-- The checks of the move at a position of a path. -/
def wOk (k : WK) (pc : Nat) : Bool :=
  match wSpec pc with
  | none => true
  | some sp => !inIvs (wIvs k) pc ||
    (sp.item.reads.all (· ∈ wKeys k pc) &&
      (wKeys k (pc + 1)).all (fun r => sp.item.writes.contains r || (wKeys k pc).contains r) &&
      (inIvs (wIvs k) (pc + 1) || evAtB kernel (pc + 1)) &&
      (pc != 1122 || (wKeys k 1123).all fun r => !(r == 332 || (334 ≤ r && r < 397))))

theorem wokc_all : (List.range 1251).all wOkC = true := by decide +kernel
theorem wok_a : (List.range 1251).all (wOk .a) = true := by decide +kernel
theorem wok_p : (List.range 1251).all (wOk .p) = true := by decide +kernel
theorem wok_b : (List.range 1251).all (wOk .b) = true := by decide +kernel

theorem wok_all : ∀ k, (List.range 1251).all (wOk k) = true
  | .a => wok_a
  | .p => wok_p
  | .b => wok_b

theorem wSpec_lt {pc : Nat} {sp : WSp} (h : wSpec pc = some sp) : pc < 1251 := by
  unfold wSpec at h
  split_ifs at h <;> omega

theorem wok_of (k : WK) {pc : Nat} {sp : WSp} (h : wSpec pc = some sp) :
    wOkC pc = true ∧ wOk k pc = true :=
  ⟨List.all_eq_true.mp wokc_all pc (List.mem_range.mpr (wSpec_lt h)),
    List.all_eq_true.mp (wok_all k) pc (List.mem_range.mpr (wSpec_lt h))⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

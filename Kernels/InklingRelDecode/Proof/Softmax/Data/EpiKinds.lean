-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Gen.EpiPack
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Decline
public import Kernels.InklingRelDecode.Proof.Lib.WinSet
public import Lemmas.Flow.OutKinds
import Lemmas.Flow.Widen

@[expose] public section

/-! # The epilogue's products are not declined

The 33 packs of pcs 2609 to 2641 pair the 64 words the accumulator load returned (registers 1763 to
1826, numbers) and the reciprocal (register 1761, a number) into registers 2346 to 2378, pairs of
numbers (`kRun`). The 32 products of pcs 2642 to 2673 multiply the pair of the reciprocal by each
pair of words: the product of two pairs of numbers is defined. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

set_option maxRecDepth 100000

noncomputable section

/-- The kinds at the start of the packs: the words and the reciprocal are numbers. -/
def epiK : Nat → Kd := fun r => if r = 1761 ∨ (1763 ≤ r ∧ r < 1827) then Kd.s .fl else .no

/-- The registers the packs read. -/
def epiDom : List Nat := 1761 :: (List.range 64).map (1763 + ·)

theorem epi_kOk : kOk epiK Gen.epk_items0 = true := by decide +kernel
theorem epi_out : (List.range 33).all (fun j => kOut epiK Gen.epk_items0 (2346 + j) == .pr .fl) =
    true := by decide +kernel
theorem epi_reads : xReadsB epiDom Gen.epk_items0 = true := by decide +kernel
theorem epi_local : xLocalB Gen.epk_items0 = true := by decide +kernel
theorem epi_len : Gen.epk_items0.length = 33 := by decide +kernel
theorem epi_req (V : Nat → Value) : xReq V Gen.epk_items0 = true := by rfl
theorem epi_fns : kFns Gen.epk_items0 := by
  simp [Gen.epk_items0, kFns, XItem.FnOk]

theorem epi_writes : ∀ j < 33, 2346 + j ∈ xWrites Gen.epk_items0 := by decide +kernel

theorem epi_scan : scanCode (fun pc ins =>
    !(decide (2642 ≤ pc) && decide (pc ≤ 2673)) || match ins.op with
      | .float f => arith2 .mul 2 f (.reg 2378) (.reg (2377 - (pc - 2642)))
      | _ => false) kernel.code 0 = true := by
  decide +kernel

/-- A register of the packs' outputs holds a pair of numbers. -/
theorem epi_pair {W : Nat → Value} (hW : ∀ r, (epiK r).Has (W r)) {j : Nat} (hj : j < 33) :
    (Kd.pr .fl).Has (xFinal W Gen.epk_items0 (2346 + j)) := by
  obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp (by simpa [kOk] using epi_kOk)
  have hk := (kRun_sound hK' hW epi_fns).2 (2346 + j)
  have ho := List.all_eq_true.mp epi_out j (List.mem_range.mpr hj)
  simp only [kOut, hK', Option.getD_some, beq_iff_eq] at ho
  rwa [ho] at hk

theorem mul_pair {L : Launch} {g : Nat} {t : TState} {a b : Nat} {va vb : Value}
    {f : FloatInstr} (ra : t.regs a = some va) (rb : t.regs b = some vb)
    (ha : (Kd.pr .fl).Has va) (hb : (Kd.pr .fl).Has vb)
    (h : arith2 .mul 2 f (.reg a) (.reg b) = true) : execIdealFloat L g t (.float f) ≠ none := by
  obtain ⟨-, ⟨-, x0, hx0⟩, ⟨-, x1, hx1⟩⟩ := ha
  obtain ⟨-, ⟨-, y0, hy0⟩, ⟨-, y1, hy1⟩⟩ := hb
  exact ideal_mul2 h (by rw [readERealPair_reg_val ra]; exact pairRead_of_reads hx0 hx1)
    (by rw [readERealPair_reg_val rb]; exact pairRead_of_reads hy0 hy1)
    (mulEReal_real _ _) (mulEReal_real _ _)

/-- **The products of pcs 2642 to 2673 are not declined**, at a state whose registers 2346 to 2378
hold the packs' outputs. -/
theorem epi_decl_core {L : Launch} {g : Nat} {t : TState} {W : Nat → Value}
    (hW : ∀ r, (epiK r).Has (W r))
    (hregs : ∀ j < 33, t.regs (2346 + j) = some (xFinal W Gen.epk_items0 (2346 + j)))
    (h1 : 2642 ≤ t.pc) (h2 : t.pc ≤ 2673) {i : Instr} (hc : kernel.code[t.pc]? = some i) :
    execIdealFloat L g t i.op ≠ none := by
  have hs := scanCode_get epi_scan hc
  rw [Nat.zero_add] at hs
  rcases Bool.or_eq_true_iff.1 hs with hs | hs
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hs
    omega
  cases hop : i.op with
  | float f =>
    rw [hop, show 2377 - (t.pc - 2642) = 2346 + (31 - (t.pc - 2642)) by omega] at hs
    exact mul_pair (a := 2378) (b := 2346 + (31 - (t.pc - 2642))) (hregs 32 (by omega))
      (hregs _ (by omega)) (epi_pair hW (j := 32) (by omega)) (epi_pair hW (by omega)) hs
  | _ => rw [hop] at hs; simp at hs

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

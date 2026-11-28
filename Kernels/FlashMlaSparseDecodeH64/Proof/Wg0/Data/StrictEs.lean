-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.NumEs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictLib

@[expose] public section

/-! # Conditions of the epilogue's output words

One output word of the epilogue (`pack`, `mul.f32x2`, `unpack`, `cvt.bf16x2`) is no fault when
the two loaded words read as numbers and the factor pair reads as `(f, f)` (`w0e_word`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- **The four items of an output word are no fault.** -/
theorem c_esword {p q : Nat} (hpq : p ≠ q) {a b c : Value} {x0 x1 f : ℝ} (ha : Rd a x0)
    (hb : Rd b x1) (hc : pairRead c = some (.ok ((f : EReal), (f : EReal)))) :
    (a.bytes = 4 ∧ b.bytes = 4) ∧
      (∃ v, fF mul2NL [.reg p, .reg q] [joinValue a b, c] = .ok v) ∧
      ((okVal (.bits 32 0) (fF mul2NL [.reg p, .reg q] [joinValue a b, c])).bytes = 8 ∧
        (splitValue 64 (okVal (.bits 32 0) (fF mul2NL [.reg p, .reg q] [joinValue a b, c]))).1.bytes
          = 4 ∧
        (splitValue 64 (okVal (.bits 32 0) (fF mul2NL [.reg p, .reg q] [joinValue a b, c]))).2.bytes
          = 4) ∧
      (∃ v, bfE [(splitValue 64 (okVal (.bits 32 0)
          (fF mul2NL [.reg p, .reg q] [joinValue a b, c]))).2,
        (splitValue 64 (okVal (.bits 32 0) (fF mul2NL [.reg p, .reg q] [joinValue a b, c]))).1] =
          .ok v) := by
  have e : fF mul2NL [.reg p, .reg q] [joinValue a b, c] = floatE mul2NI [joinValue a b, c] := by
    have hq : lk [p, q] [joinValue a b, c] q = c := by
      have e : (q == p) = false := beq_false_of_ne (Ne.symm hpq)
      simp [lk, List.lookup, e]
    have hp : lk [p, q] [joinValue a b, c] p = joinValue a b := by simp [lk]
    simp only [fF, regsOf, regOf, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, List.map_cons, List.map_nil, fOpnd, hp, hq, mul2NL]
  have hm := floatE_mul2N_reads (pairRead_join ha hb) hc (mulEReal_coe x0 f) (mulEReal_coe x1 f)
  have hM : okVal (.bits 32 0) (fF mul2NL [.reg p, .reg q] [joinValue a b, c]) =
      .pair (.float .f32 (x0 * f)) (.float .f32 (x1 * f)) := by
    rw [e, hm]; simp only [okVal, erealValue_coe]
  refine ⟨⟨ha.1.1, hb.1.1⟩, ⟨_, by rw [e, hm]⟩, ?_, ?_⟩
  · rw [hM]; exact upk_cond rfl rfl rfl
  · rw [hM]; exact bf_cond rfl rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

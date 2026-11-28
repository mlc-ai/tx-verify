-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal1

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

theorem add2F {d : Value} {a b : Nat} (hb : b ≠ a) {x0 x1 y0 y1 : ℝ} :
    okVal d ((fF add2NL [.reg a, .reg b]) [joinValue (.float .f32 x0) (.float .f32 x1),
      joinValue (.float .f32 y0) (.float .f32 y1)]) =
      joinValue (.float .f32 (x0 + y0)) (.float .f32 (x1 + y1)) := by
  have e : (fF add2NL [.reg a, .reg b]) [joinValue (.float .f32 x0) (.float .f32 x1),
      joinValue (.float .f32 y0) (.float .f32 y1)] = add2NE (joinValue (.float .f32 x0)
      (.float .f32 x1)) (joinValue (.float .f32 y0) (.float .f32 y1)) := by
    simp only [fF, regsOf, regOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, fOpnd, lk,
      List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hb,
      beq_self_eq_true, Option.getD_some, add2NL]
  have h0 : ∀ r : ℝ, readEReal .f32 (.float .f32 r) = some (.ok (r : EReal)) := readEReal_float
  have j : ∀ u v : ℝ,
      joinValue (.float .f32 u) (.float .f32 v) = .pair (.float .f32 u) (.float .f32 v) :=
    fun _ _ => rfl
  have e2 : add2NE (joinValue (.float .f32 x0) (.float .f32 x1)) (joinValue (.float .f32 y0)
      (.float .f32 y1)) = .ok (.pair (.float .f32 (x0 + y0)) (.float .f32 (x1 + y1))) := by
    unfold add2NE
    simp only [j, idealAdd2, pairRead, splitValue, h0, bindRead, addEReal_coe, pure, Except.pure,
      erealValue_coe]
  rw [e, e2, j]
  rfl

theorem selp_float {dd a b p : Nat} (hab : b ≠ a) (hpa : p ≠ a) (hpb : p ≠ b) (q : Bool)
    (u : ℝ) (d : Value) :
    okVal d (coreF (.int ⟨.selp, .float .f32, false, [some dd], [.reg a, .reg b, .reg p]⟩) [a, b, p]
      [.float .f32 u, .float .f32 u, .pred q]) = .float .f32 u := by
  unfold coreF coreW
  have hb : lk [a, b, p] [Value.float .f32 u, .float .f32 u, .pred q] b = .float .f32 u := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  have ha : lk [a, b, p] [Value.float .f32 u, .float .f32 u, .pred q] a = .float .f32 u := by
    simp [lk]
  have hp : lk [a, b, p] [Value.float .f32 u, .float .f32 u, .pred q] p = .pred q := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hpa,
      beq_false_of_ne hpb, beq_self_eq_true, Option.getD_some]
  have h4 : FloatFmt.f32.bytes = 4 := rfl
  cases q <;> simp [h4, hp, hb, ha, oVal, Value.bytes, DType.width, pure, Except.pure, okVal,
    bind, Except.bind]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

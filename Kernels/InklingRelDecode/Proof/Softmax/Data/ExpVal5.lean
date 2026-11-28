-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal4
public import Kernels.InklingRelDecode.Proof.Softmax.Data.PkTyped

@[expose] public section

/-! # The words of the probability store

Word `c` of the store (register `1677 + c`) is the `bf16` pair of the exponentials of the shifted
scores `X (1288 + 4 c)` and `X (1290 + 4 c)`, from the exponent window's words. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
noncomputable section

/-- The word `c` of the probability store. -/
def pWord (X : Nat → EReal) (c : Nat) : Value :=
  .pair (.float .bf16 (pw2 (X (1288 + 4 * c)))) (.float .bf16 (pw2 (X (1290 + 4 * c))))

theorem cvtL {d : Value} {x y : ℝ} :
    okVal d (cvtBfL [.float .f32 x, .float .f32 y]) = .pair (.float .bf16 y) (.float .bf16 x) := by
  simp only [cvtBfL, cvtBfE_float, okVal]

/-- **The pack's words**: the first run's registers and the second's. -/
theorem pk_words {W : Nat → Value} {X : Nat → EReal}
    (h1 : ∀ r, 1994 ≤ r → r < 2018 → W r = pairTab X (r - 1994))
    (h2 : ∀ r, 508 ≤ r → r < 524 → W r = singTab X (r - 508)) :
    (∀ p ∈ Gen.pk1_facts2 W, p.2 = pWord X (p.1 - 1677)) ∧
      ∀ p ∈ Gen.pk2_facts1 W, p.2 = pWord X (p.1 - 1677) := by
  constructor <;> intro p hp
  all_goals
    simp only [Gen.pk1_facts2, Gen.pk2_facts1, List.mem_cons, List.not_mem_nil] at hp
    repeat' rcases hp with rfl | hp
    all_goals
      simp (disch := first | decide | decide +kernel) only [
      Gen.pk1_v951_0, Gen.pk1_v951_1, Gen.pk1_v952, Gen.pk1_v953_0, Gen.pk1_v953_1,
      Gen.pk1_v954, Gen.pk1_v955_0, Gen.pk1_v955_1, Gen.pk1_v956, Gen.pk1_v957_0,
      Gen.pk1_v957_1, Gen.pk1_v958, Gen.pk1_v959_0, Gen.pk1_v959_1, Gen.pk1_v960,
      Gen.pk1_v961_0, Gen.pk1_v961_1, Gen.pk1_v962, Gen.pk1_v963_0, Gen.pk1_v963_1,
      Gen.pk1_v964, Gen.pk1_v965_0, Gen.pk1_v965_1, Gen.pk1_v966, Gen.pk1_v967_0,
      Gen.pk1_v967_1, Gen.pk1_v968, Gen.pk1_v969_0, Gen.pk1_v969_1, Gen.pk1_v970,
      Gen.pk1_v971_0, Gen.pk1_v971_1, Gen.pk1_v972, Gen.pk1_v973_0, Gen.pk1_v973_1,
      Gen.pk1_v974, Gen.pk1_v975_0, Gen.pk1_v975_1, Gen.pk1_v976, Gen.pk1_v977_0,
      Gen.pk1_v977_1, Gen.pk1_v978, Gen.pk1_v979_0, Gen.pk1_v979_1, Gen.pk1_v980,
      Gen.pk1_v981_0, Gen.pk1_v981_1, Gen.pk1_v982, Gen.pk1_v983_0, Gen.pk1_v983_1,
      Gen.pk1_v984, Gen.pk1_v985_0, Gen.pk1_v985_1, Gen.pk1_v986, Gen.pk1_v987_0,
      Gen.pk1_v987_1, Gen.pk1_v988, Gen.pk1_v989_0, Gen.pk1_v989_1, Gen.pk1_v990,
      Gen.pk1_v991_0, Gen.pk1_v991_1, Gen.pk1_v992, Gen.pk1_v993_0, Gen.pk1_v993_1,
      Gen.pk1_v994, Gen.pk1_v995_0, Gen.pk1_v995_1, Gen.pk1_v996, Gen.pk1_v997_0,
      Gen.pk1_v997_1, Gen.pk1_v998, Gen.pk2_v1000, Gen.pk2_v1001, Gen.pk2_v1002, Gen.pk2_v1003,
      Gen.pk2_v1004, Gen.pk2_v1005, Gen.pk2_v1006, Gen.pk2_v1007, pairTab, singTab, pWord,
      split_pair, cvtL, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceSub,
      h1, h2, swTab, List.getD_cons_zero, List.getD_cons_succ]

/-- **The words of the store, from the shifted scores**: word `c` of the pack that follows the
exponent window run on the registers `W`. -/
theorem p_words {W : Nat → Value} {X : Nat → EReal} (hx : ∀ r ∈ xRegs, Ev (W r) (X r))
    (hy : ∀ r, 1271 ≤ r → r < 1287 → W r = .float .f32 (pw2 (X (swTab (r - 1271)))))
    {q q' : Bool}
    (hq : W 179 = .pred q) (hq' : W 180 = .pred q') :
    ∀ c < 32, vP2 (vP1 (runE2.V' W)) (1677 + c) = pWord X (1677 + c - 1677) := by
  have e2 : ∀ x ∈ runE2.outs, (1994 ≤ x → x < 2018 → runE2.V' W x = pairTab X (x - 1994)) ∧
      (508 ≤ x → x < 524 → runE2.V' W x = singTab X (x - 508)) := fun x hx' =>
    V'_out runE2 runE2_ok (P := fun r v => (1994 ≤ r → r < 2018 → v = pairTab X (r - 1994)) ∧
      (508 ≤ r → r < 524 → v = singTab X (r - 508))) (W := W)
      (fun p hp => let h := e2_regs hx hy hq hq' p hp; ⟨h.1, h.2.1⟩) hx'
  have m1 : ∀ x, 1994 ≤ x → x < 2018 → x ∈ runE2.outs := by decide +kernel
  have m2 : ∀ x, 508 ≤ x → x < 524 → x ∈ runE2.outs := by decide +kernel
  have h1 : ∀ r, 1994 ≤ r → r < 2018 → runE2.V' W r = pairTab X (r - 1994) := fun r a b =>
    (e2 r (m1 r a b)).1 a b
  have n2 : ∀ x, 508 ≤ x → x < 524 → x ∉ runK1.outs := by decide +kernel
  have n1 : ∀ x, 1994 ≤ x → x < 2018 → x ∉ runK1.outs := by decide +kernel
  have h2 : ∀ r, 508 ≤ r → r < 524 → vP1 (runE2.V' W) r = singTab X (r - 508) := fun r a b => by
    rw [vP1, V'_notin runK1 runK1_ok _ (n2 r a b)]
    exact (e2 r (m2 r a b)).2 a b
  have p1 := pk_words (W := runE2.V' W) h1 (fun r a b => by
    rw [← h2 r a b, vP1, V'_notin runK1 runK1_ok _ (n2 r a b)])
  have p2 := (pk_words (W := vP1 (runE2.V' W)) (fun r a b => by
    rw [vP1, V'_notin runK1 runK1_ok _ (n1 r a b)]; exact h1 r a b) h2).2
  intro c hc
  have hr : 1677 + c ∈ kTm := by
    have : ∀ c < 32, 1677 + c ∈ kTm := by decide +kernel
    exact this c hc
  rcases List.mem_append.mp hr with k1 | k2
  · have hn : 1677 + c ∉ runK2.outs := by
      have : ∀ x ∈ runK1.outs, x ∉ runK2.outs := by decide +kernel
      exact this _ k1
    rw [vP2, V'_notin runK2 runK2_ok _ hn]
    exact V'_out runK1 runK1_ok (P := fun r v => v = pWord X (r - 1677)) p1.1 k1
  · exact V'_out runK2 runK2_ok (P := fun r v => v = pWord X (r - 1677)) p2 k2

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

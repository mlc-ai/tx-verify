-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.IntWord
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Fin

@[expose] public section

/-! # The mask runs on exact scores

The mask of the first window (`runB`, pcs 1467 to 1599, and `runC`, pcs 1600 to 1755) keeps the
score of column `c` of the thread's 64 when `cO + b + c <= P`, with `cO` the thread's column
offset (registers 1901), `b` the block's first key (1912) and `P` the last visible key (the
constants of registers 1961 to 1992 hold `P - 2u` and `P - 2u - 1`, the odd one of the first
pair as `cO - P`). The runs compute the signed 32-bit differences and select the score or `-inf`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- The word is that of the integer. -/
def IW (v : Value) (z : ℤ) : Prop := v = w32 z

/-- The difference column `c` is tested with (the odd column of the first pair is special). -/
def zc (cO b P : ℤ) (c : Nat) : ℤ := if c = 1 then cO - P + b else P - c - (cO + b)

/-- Whether column `c` passes the test. -/
def vis (cO b P : ℤ) (c : Nat) : Bool :=
  if c = 1 then decide (sg (zc cO b P 1) < 0) else decide (0 ≤ sg (zc cO b P c))

/-- The column a predicate register 98 to 133 tests. -/
def colOfPred (p : Nat) : Nat := 62 - 2 * ((p - 98) / 2) + (p - 98) % 2

/-- The registers of the differences of the first 28 columns. -/
def IsSub (r : Nat) : Prop :=
  r = 1014 ∨ r = 1015 ∨ r = 1018 ∨ (1021 ≤ r ∧ r ≤ 1066 ∧ (r - 1021) % 4 < 2)

instance : DecidablePred IsSub := fun r => by unfold IsSub; infer_instance

/-- The column a difference register belongs to. -/
def colOfSub (r : Nat) : Nat :=
  if r = 1018 then 0 else if r = 1015 then 2 else if r = 1014 then 3
  else 2 * ((r - 1021) / 4) + (if (r - 1021) % 4 = 0 then 5 else 4)

/-- **What the mask runs read**: the column offset, the block's first key, the constants. -/
structure MaskIn (W : Nat → Value) (cO b P : ℤ) : Prop where
  col : IW (W 1901) cO
  base : IW (W 1912) b
  cst : ∀ u < 32, W (1961 + u) = joinValue (w32 (P - 2 * u))
    (w32 (if u = 0 then cO - P else P - 2 * u - 1))

theorem add_iw {d a b : Nat} (hab : b ≠ a) {x y : Value} {p q : ℤ} (hx : IW x p) (hy : IW y q)
    (v : Value) : IW (okVal v (coreF (.int ⟨.add, .int .s 32, false, [some d],
      [.reg a, .reg b]⟩) [a, b] [x, y])) (p + q) := by
  rw [hx, hy]; exact add_w hab p q v

theorem sub_iw {d a b : Nat} (hab : b ≠ a) {x y : Value} {p q : ℤ} (hx : IW x p) (hy : IW y q)
    (v : Value) : IW (okVal v (coreF (.int ⟨.sub, .int .s 32, false, [some d],
      [.reg a, .reg b]⟩) [a, b] [x, y])) (p - q) := by
  rw [hx, hy]; exact sub_w hab p q v

theorem gt_p {d a : Nat} {x : Value} {z : ℤ} {b : Bool} (hx : IW x z) (hb : decide (0 ≤ sg z) = b)
    (v : Value) : okVal v (coreF (.int ⟨.setp .gt none, .int .s 32, false, [some d],
      [.reg a, .imm (-1)]⟩) [a] [x]) = .pred b := by
  rw [hx, setp_gt_w, hb]

theorem lt_p {d a : Nat} {x : Value} {z : ℤ} {b : Bool} (hx : IW x z) (hb : decide (sg z < 0) = b)
    (v : Value) : okVal v (coreF (.int ⟨.setp .lt none, .int .s 32, false, [some d],
      [.reg a, .imm 0]⟩) [a] [x]) = .pred b := by
  rw [hx, setp_lt_w, hb]

theorem selp_ev' {d a p : Nat} (hp : p ≠ a) {pv w : Value} {q : Bool} {x : EReal}
    (hq : pv = .pred q) (h : Ev w x) (v : Value) :
    Ev (okVal v (coreF (.int ⟨.selp, .float .f32, false, [some d],
      [.reg a, .f32imm 4286578688, .reg p]⟩) [a, p] [w, pv])) (if q then x else ⊥) := by
  rw [hq]; exact selp_ev hp q h v

theorem clean_w32 (z : ℤ) : Clean (w32 z) := by
  refine ⟨rfl, nofun, ?_⟩
  intro w x h
  have e : x = truncBits 32 (BitVec.ofInt 64 z) := (Value.bits.inj h).2.symm
  rw [e, toNat_w]
  have h5 : z % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  have h4 : 0 ≤ z % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  omega

theorem lo_iw {W : Nat → Value} {cO b P : ℤ} (h : MaskIn W cO b P) {r : Nat} (h1 : 1961 ≤ r)
    (h2 : r < 1993) : IW (splitValue 64 (W r)).1 (P - 2 * ((r : ℤ) - 1961)) := by
  have e := h.cst (r - 1961) (by omega)
  rw [show 1961 + (r - 1961) = r by omega] at e
  rw [e, split_join_clean (clean_w32 _) (clean_w32 _)]
  unfold IW
  dsimp only
  congr 1
  omega

theorem hi_iw {W : Nat → Value} {cO b P : ℤ} (h : MaskIn W cO b P) {r : Nat} (h1 : 1961 ≤ r)
    (h2 : r < 1993) : IW (splitValue 64 (W r)).2
      (if r = 1961 then cO - P else P - 2 * ((r : ℤ) - 1961) - 1) := by
  have e := h.cst (r - 1961) (by omega)
  rw [show 1961 + (r - 1961) = r by omega] at e
  rw [e, split_join_clean (clean_w32 _) (clean_w32 _)]
  unfold IW
  dsimp only
  congr 1
  split_ifs <;> omega

theorem pe_lo {v : Value} {x y : EReal} (h : PE v x y) : Ev (splitValue 64 v).1 x := by
  obtain ⟨a, b, e, ha, -⟩ := h
  rw [e]; exact ha

theorem pe_hi {v : Value} {x y : EReal} (h : PE v x y) : Ev (splitValue 64 v).2 y := by
  obtain ⟨a, b, e, -, hb⟩ := h
  rw [e]; exact hb

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondPeer
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.NumLo

@[expose] public section

/-! # The words a peer store writes

The register a peer store `k` (pc `403 + 10 k`) reads holds the 128-bit pack of the block's low
words `4 k .. 4 k + 3`, the first word lowest (`pst_reg0` .. `pst_reg7`): the pack widens,
shifts and merges four `halfB` words, and `coreF_pack` joins the two pairs. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

noncomputable section

/-- The pack of two pairs of words is the pair of the pairs. -/
theorem coreF_pack {op : Op} {r1 r2 d : Nat} {ty : DType} {a b c e : Value}
    (hop : op = .move ⟨.pack, ty, [some d], [.reg r1, .reg r2]⟩) (hty : ty.width = 128)
    (hne : r1 ≠ r2) (ha : a.bytes = 4) (hb : b.bytes = 4) (hc : c.bytes = 4) (he : e.bytes = 4) :
    coreF op [r1, r2] [.pair a b, .pair c e] = .ok (.pair (.pair a b) (.pair c e)) := by
  subst hop
  have hl1 : lk [r1, r2] [.pair a b, .pair c e] r1 = .pair a b := by
    simp [lk]
  have h21 : (r2 == r1) = false := beq_false_of_ne (Ne.symm hne)
  have hl2 : lk [r1, r2] [.pair a b, .pair c e] r2 = .pair c e := by
    simp [lk, List.lookup, h21]
  have h8 : (Value.pair a b).bytes = 8 := by simp [Value.bytes, ha, hb]
  have h8' : (Value.pair c e).bytes = 8 := by simp [Value.bytes, hc, he]
  simp [coreF, coreW, oVal, hl1, hl2, hty, h8, h8', joinValue, pure, Except.pure, bind,
    Except.bind]

open Lean in
set_option hygiene false in
/-- `pk<n>_value` of the `k`th peer store (`n = 394 + 10 k`): the pack of four `halfB` words. -/
local macro "pk_value " k:num : command => do
  let k := k.getNat
  let n := 394 + 10 * k
  let id (s : String) := mkIdent (.mkSimple s)
  let v (i : Nat) := id s!"pk{n}_v{i}"
  let num (i : Nat) := Syntax.mkNumLit (toString i)
  let a := 2886 + 4 * k
  let r := 3183 + 8 * k
  `(theorem $(id s!"pk{n}_value") (V : Nat → Value) (h0 : halfB (V $(num a)) = true)
      (h1 : halfB (V $(num (a + 1))) = true) (h2 : halfB (V $(num (a + 2))) = true)
      (h3 : halfB (V $(num (a + 3))) = true) :
      $(v (n + 8)) V = .pair (.pair (V $(num a)) (V $(num (a + 1))))
        (.pair (V $(num (a + 2))) (V $(num (a + 3)))) := by
    have e1 : $(v (n + 7)) V = .pair (V $(num (a + 2))) (V $(num (a + 3))) := by
      unfold $(v (n + 7)) $(v (n + 2)) $(v (n + 1)) $(v n)
      exact pkMge (by decide) h3 h2
    have e0 : $(v (n + 6)) V = .pair (V $(num a)) (V $(num (a + 1))) := by
      unfold $(v (n + 6)) $(v (n + 5)) $(v (n + 4)) $(v (n + 3))
      exact pkMlt (by decide) h1 h0
    unfold $(v (n + 8))
    rw [e0, e1]
    rw [coreF_pack (op := $(id s!"pk{n}_op{n + 8}")) (r1 := $(num r)) (r2 := $(num (r + 1)))
      rfl rfl (by decide) (halfB_bytes h0) (halfB_bytes h1) (halfB_bytes h2) (halfB_bytes h3)]
    rfl)

open Lean in
set_option hygiene false in
/-- `pst_reg<k>`: register `4031 + k` of peer store `k` holds the pack of the low words `4 k ..`. -/
local macro "pst_reg " k:num : command => do
  let k := k.getNat
  let n := 394 + 10 * k
  let id (s : String) := mkIdent (.mkSimple s)
  let num (i : Nat) := Syntax.mkNumLit (toString i)
  let a := 2886 + 4 * k
  let prev := if k = 0 then id "m_vm" else id s!"f_pst{k - 1}"
  let lo (i : Nat) := Syntax.mkNumLit (toString (4 * k + i))
  let at_ := id s!"w0c_lo_at{k}"
  let f := id s!"f_pst{k}"
  let facts := id s!"pk{n}_facts1"
  let vv := id s!"pk{n}_v{n + 8}"
  let val := id s!"pk{n}_value"
  `(theorem $(id s!"pst_reg{k}") {x : BitVec 64} {m l mx sk : Value} {lo hi : List Value}
      {mw : Value} (hlen : lo.length = 32)
      (h : ∀ c < 32, halfB (lo.getD c (.pred false)) = true) :
      lookupD ($f x m l mx sk lo hi mw) $(num (4031 + k)) =
        .pair (.pair (lo.getD $(lo 0) (.pred false)) (lo.getD $(lo 1) (.pred false)))
          (.pair (lo.getD $(lo 2) (.pred false)) (lo.getD $(lo 3) (.pred false))) := by
    unfold $f
    rw [lk_head_mem (by simp only [$facts:ident, List.map_cons, List.map_nil]; decide)]
    have a0 : lookupD ($prev x m l mx sk lo hi mw) $(num a) = lo.getD $(lo 0) (.pred false) :=
      $at_ hlen $(lo 0) (by norm_num) (by norm_num)
    have a1 : lookupD ($prev x m l mx sk lo hi mw) $(num (a + 1)) = lo.getD $(lo 1) (.pred false) :=
      $at_ hlen $(lo 1) (by norm_num) (by norm_num)
    have a2 : lookupD ($prev x m l mx sk lo hi mw) $(num (a + 2)) = lo.getD $(lo 2) (.pred false) :=
      $at_ hlen $(lo 2) (by norm_num) (by norm_num)
    have a3 : lookupD ($prev x m l mx sk lo hi mw) $(num (a + 3)) = lo.getD $(lo 3) (.pred false) :=
      $at_ hlen $(lo 3) (by norm_num) (by norm_num)
    have hk : lookupD ($facts (lookupD ($prev x m l mx sk lo hi mw))) $(num (4031 + k)) =
        $vv (lookupD ($prev x m l mx sk lo hi mw)) := by
      simp [$facts:ident, lookupD]
    rw [hk, $val _ (by rw [a0]; exact h _ (by norm_num)) (by rw [a1]; exact h _ (by norm_num))
      (by rw [a2]; exact h _ (by norm_num)) (by rw [a3]; exact h _ (by norm_num)), a0, a1, a2, a3])

pk_value 0
pk_value 1
pk_value 2
pk_value 3
pk_value 4
pk_value 5
pk_value 6
pk_value 7

pst_reg 0
pst_reg 1
pst_reg 2
pst_reg 3
pst_reg 4
pst_reg 5
pst_reg 6
pst_reg 7

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

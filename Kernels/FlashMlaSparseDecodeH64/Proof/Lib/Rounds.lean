-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Arith
public import Lemmas.Flow.Arith32Wide
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # The block count of a CTA, as a function of the launch

Every role that runs the block loop loads the row's two lengths (`%ctaid.y` is the row): the
top-k length and the extra top-k length, each the parameter (`topk`, `extra_topk`) unless its
length pointer is set, then the row's word of the length array (`lenWA`, `lenWB`). From the two
words each role computes the padded total and the block count with the same 32-bit code
(`roundsOf`: none for a padded total below 64). `blocksOf P L c` is that count for CTA `c`: the
count the roles' machines use (`Common/RoleWords.lean` ties each role's loaded words to `lenWA`,
`lenWB`), so a cross-role fact about the ring uses of a CTA has one block count. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The row (`%ctaid.y`) of CTA `c`. -/
def rowOf (L : Launch) (c : Nat) : Nat := (L.ctaidOf c).y % 2 ^ 32

theorem rowOf_cta (L : Launch) (g : Nat) : rowOf L (g / L.block) = ctaidY L g := rfl

/-- The top-k length word of CTA `c`: the parameter unless the pointer is set. -/
def lenWA (P : Params) (L : Launch) (c : Nat) : BitVec 64 :=
  if eqz64 (pw8 (P.topkLenBase.getD 0)) then pw P.topk else W (P.topkLen (rowOf L c))

/-- The extra top-k length word of CTA `c`: the parameter unless the pointer is set. -/
def lenWB (P : Params) (L : Launch) (c : Nat) : BitVec 64 :=
  if eqz64 (pw8 (P.extraTopkLenBase.getD 0)) then pw P.extra_topk
  else W (P.extraTopkLen (rowOf L c))

/-- The padded length `pad64 a`. -/
abbrev padL (a : BitVec 64) : BitVec 64 :=
  andi (add32 (addi a 63) (shru (shrs (addi a 63) 31) 26)) (-64)
/-- The padded total of the two lengths, as the code computes it. -/
abbrev totL (a b : BitVec 64) : BitVec 64 :=
  add32 (add32 (addi b 63) (max32 (padL a) (i32 64))) (sub32 (padL b) (addi b 63))
/-- The block count word. -/
abbrev nblkL (a b : BitVec 64) : BitVec 64 :=
  shrs (add32 (totL a b) (shru (shrs (totL a b) 31) 26)) 6

/-- The blocks two length words give (none for a padded total below 64). -/
def roundsOf (a b : BitVec 64) : Nat :=
  if scmpi .lt .s (totL a b) 64 then 0 else (nblkL a b).toNat

private theorem tr32 (v : BitVec 64) : (truncBits 32 v).toNat = v.toNat % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

/-- Adding `x` and subtracting it again, in 32-bit words. -/
theorem add32_sub32 (x y z : BitVec 64) : add32 (add32 x z) (sub32 y x) = add32 y z := by
  apply BitVec.eq_of_toNat_eq
  simp only [add32, sub32, r32, tr32, BitVec.toNat_add, BitVec.toNat_sub]
  generalize x.toNat = a
  generalize y.toNat = b
  generalize z.toNat = c
  omega

/-- The padded total is the padded second length plus `max(pad64 a, 64)`. -/
theorem totL_eq (a b : BitVec 64) : totL a b = add32 (padL b) (max32 (padL a) (i32 64)) :=
  add32_sub32 _ _ _

/-- **The block count of CTA `c`**: the blocks of its row's two length words. -/
def blocksOf (P : Params) (L : Launch) (c : Nat) : Nat := roundsOf (lenWA P L c) (lenWB P L c)

/-- **Every CTA is inside the batch**: the code's test `%ctaid.y >= b` (the early return of each
role) fails. -/
theorem batch_in {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) (g : Nat) :
    scmp .ge .s (r2W L g) (pw P.b) = false := by
  have h := (ctaid_lt hp g).2
  have := hp.bLt
  have h2 : ctaidY L g < 2 ^ 32 := by omega
  simp [scmp, r2W, pw, leNat_eq, PTX.compare, r32, truncBits, toSigned]
  split_ifs <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

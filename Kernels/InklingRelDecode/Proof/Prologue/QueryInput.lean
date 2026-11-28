-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Values
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
import Lemmas.Flow.Arith32Word

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Arith32 Control

private theorem sx_small (n : Nat) (h : n < 2 ^ 31) : Lib.sx n = n := by
  unfold Lib.sx; omega

/-- The token of a row group is the row divided by six. -/
theorem qTok_eq (tid gp : Nat) (hgp : gp < 4) : qTok tid gp = (tid / 8 % 16 + 16 * gp) / 6 := by
  unfold qTok qRow
  omega

/-- The head of a row group: its offset in the sixth is below six. -/
theorem qSum_mod (tid gp : Nat) (hgp : gp < 4) :
    qSum tid gp % 8 = (tid / 8 % 16 + 16 * gp) % 6 := by
  unfold qSum
  rw [qTok_eq tid gp hgp]
  split_ifs with h <;> omega

/-- The query load address is the input byte address of its Q element. -/
theorem qLane_eq {Q : Params} {first : Value} {r tid y gp e : Nat}
    (hs : Q.strideQ < 2 ^ 31) (hf : first = b32 (Q.qStart r))
    (hx : Q.qStart r + qTok tid gp < 2 ^ 31) (hy : y < 2) (hgp : gp < 4) (he : e < 16)
    (hlt : Q.qBase + 2 * ((Q.qStart r + qTok tid gp) * Q.strideQ +
      (y * 6 + (tid / 8 % 16 + 16 * gp) % 6) * 128 + (8 * (tid % 8) + e % 8 + 64 * (e / 8))) <
        2 ^ 64) :
    qLane Q first tid y gp e = Q.qBase + 2 * ((Q.qStart r + qTok tid gp) * Q.strideQ +
      (y * 6 + (tid / 8 % 16 + 16 * gp) % 6) * 128 + (8 * (tid % 8) + e % 8 + 64 * (e / 8))) := by
  have w : (Lib.word first).toNat = Q.qStart r % 2 ^ 32 := by
    subst hf
    simp [Lib.word, b32, Value.regBits, truncBits, BitVec.toNat_ofNat]
    omega
  have prod : qProd Q first tid gp = (Q.qStart r + qTok tid gp) * Q.strideQ := by
    unfold qProd
    rw [w, Nat.mod_eq_of_lt (by omega : Q.qStart r < 2 ^ 32), sx_small _ hx, sx_small _ hs,
      Nat.mul_comm]
  have rem := qSum_mod tid gp hgp
  have hq := qTok_eq tid gp hgp
  have hh : (y * 6 + qSum tid gp % 8) % 2 ^ 32 * 128 % 2 ^ 32 =
      (y * 6 + qSum tid gp % 8) * 128 := by
    omega
  unfold qLane queryPointer queryOrigin qHoff qOff
  rw [prod, hh, rem]
  have : 0 ≤ tid := Nat.zero_le _
  omega

/-- The word difference of two request words is the length of the request. -/
theorem qlen_word {Q : Params} {d : D} {r : Nat} (hf : d.first = b32 (Q.qStart r))
    (hl : d.last = b32 (Q.qStart (r + 1))) (hm : Q.qStart r ≤ Q.qStart (r + 1))
    (hb : Q.qStart (r + 1) < 2 ^ 31) : qlen d = W (Q.qLen r) := by
  unfold qlen subValue
  rw [hf, hl]
  have e : Q.qLen r = Q.qStart (r + 1) - Q.qStart r := rfl
  rw [e]
  generalize Q.qStart r = A at *
  generalize Q.qStart (r + 1) = B at *
  apply BitVec.eq_of_toNat_eq
  simp only [Lib.word, Value.regBits, b32, sub32, truncBits, Option.getD_some,
    BitVec.toNat_ofNat, BitVec.toNat_sub, W]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue

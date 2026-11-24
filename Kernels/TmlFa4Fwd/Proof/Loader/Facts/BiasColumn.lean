-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.TcSpec
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.BiasNum
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Flow PTX.Flow.Arith32
set_option maxRecDepth 20000

def columnWord (tt : Fin 7) (q : Fin 2) (gap rnd warm : BitVec 64) : BitVec 64 :=
  let x := if q=0 then i32 1152 else i32 1216
  let y := if q=0 then i32 1024 else i32 1088
  match tt with
  | 1 => sub32 x (shl (max32 gap (i32 0)) 7)
  | 3 => x
  | 4 => addi (shl (sub32 (shru gap 31) (add32 (max32 gap (i32 0)) rnd)) 7)
      (if q=0 then 1024 else 1088)
  | 5 => sub32 y (shl rnd 7)
  | 6 => sub32 x (shl warm 7)
  | _ => if q=0 then i32 0 else i32 64

theorem bias_col_reg {p L g w ent v k t} (tt : Fin 7) (q : Fin 2)
    (hat : (code p L g w ent).AtD ⟨.tc tt q,v,k⟩ t) :
    t.regs (inputSite (siteOf tt q)).colReg =
      some (.bits 32 (columnWord tt q v.su.r29 v.rnd (warmRounds v))) := by
  fin_cases tt <;> fin_cases q <;> exact lreg hat (by lit_mem) rfl

/-- Signed origin column of a bias box. Only a later stage-zero group can be shifted. -/
def biasOriginCol (short : Bool) (st q : Fin 2) (u : Nat) : Int :=
  1152+64*(q.val : Int)-128*(u : Int)+(if short ∧ st=0 ∧ u≠0 then 128 else 0)

private def signedCol (x : BitVec 64) := (BitVec.ofNat 32 (truncBits 32 x).toNat).toInt

private theorem last_word (q : Fin 2) (gap rnd warm : BitVec 64) :
    columnWord 6 q gap rnd warm = columnWord 6 q (i32 (-1)) 0 warm := by simp only [columnWord]

private theorem prime_cols (s : Bool) (q : Fin 2) :
    signedCol (columnWord 1 q (if s then i32 (-1) else i32 0) 0 0) = biasOriginCol s 0 q 0 ∧
    signedCol (columnWord 3 q (if s then i32 (-1) else i32 0) 0 0) = biasOriginCol s 1 q 0 := by
  cases s <;> fin_cases q <;> decide

private theorem warm_cols : ∀ (s : Bool) (q : Fin 2) (r : Fin 10),
    signedCol (columnWord 4 q (if s then i32 (-1) else i32 0) (W r.val) 0) =
      biasOriginCol s 0 q (1+r.val) ∧
    signedCol (columnWord 5 q (if s then i32 (-1) else i32 0) (W r.val) 0) =
      biasOriginCol s 1 q (1+r.val) ∧
    signedCol (columnWord 6 q (i32 (-1)) 0 (W r.val)) = biasOriginCol true 0 q (1+r.val) := by
  decide +kernel

private theorem last_cols (q : Fin 2) (n : Nat) (h : n<10) :
    signedCol (columnWord 6 q (i32 (-1)) 0 (W n)) = biasOriginCol true 0 q (1+n) :=
  (warm_cols true q ⟨n,h⟩).2.2

/-- The ledger's poll count identifies the group and hence the signed column word. -/
theorem bias_col_of_count {L g v k n} (tt : Fin 7) (st q : Fin 2) (short : Bool) {u : Nat}
    (off : taOff tt = 320+8*st.val)
    (gap : v.su.r29 = if short then i32 (-1) else i32 0)
    (poll : n (nE L g (decide (st=1))) = u+1)
    (hn : BiasNum L g ((⟨.tc tt q,v,k⟩ : D),n))
    (hr : Rounds (.tc tt q) v (n .commit)) :
    (BitVec.ofNat 32 (truncBits 32 (columnWord tt q v.su.r29 v.rnd (warmRounds v))).toNat).toInt =
      biasOriginCol short st q u := by
  obtain ⟨r31,round⟩ := hr
  obtain ⟨fixed,loop,last,_⟩ := hn (decide (st=1))
  have cases' : (tt=1 ∧ st=0) ∨ (tt=3 ∧ st=1) ∨ (tt=4 ∧ st=0) ∨
      (tt=5 ∧ st=1) ∨ (tt=6 ∧ st=0) := by
    have table : ∀ (t : Fin 7) (s : Fin 2), taOff t = 320+8*s.val →
      (t=1 ∧ s=0) ∨ (t=3 ∧ s=1) ∨ (t=4 ∧ s=0) ∨ (t=5 ∧ s=1) ∨ (t=6 ∧ s=0) := by decide
    exact table tt st off
  change signedCol _ = _
  rw [gap]
  rcases cases' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have cnt := fixed 1 rfl
    change n (nE L g false) = u+1 at poll
    change (n (nE L g false) : Int) = 1 at cnt
    rw [poll] at cnt
    obtain rfl : u=0 := by omega
    exact (prime_cols short q).1
  · have cnt := fixed 1 rfl
    change n (nE L g true) = u+1 at poll
    change (n (nE L g true) : Int) = 1 at cnt
    rw [poll] at cnt
    obtain rfl : u=0 := by omega
    exact (prime_cols short q).2
  · obtain ⟨r,er,_,lt,num⟩ := round
    have cnt := loop 1 rfl
    change n (nE L g false) = u+1 at poll
    change 2*(n (nE L g false) : Int) = n .commit+1 at cnt
    rw [poll] at cnt
    change n .commit = 2+2*r+1 at num
    have lt' := wRn_le v.su.r28
    rw [er,show u=1+r by omega]
    exact (warm_cols short q ⟨r,by omega⟩).1
  · obtain ⟨r,er,_,lt,num⟩ := round
    have cnt := loop 1 rfl
    change n (nE L g true) = u+1 at poll
    change 2*(n (nE L g true) : Int) = n .commit+1 at cnt
    rw [poll] at cnt
    change n .commit = 2+2*r+1 at num
    have lt' := wRn_le v.su.r28
    rw [er,show u=1+r by omega]
    exact (warm_cols short q ⟨r,by omega⟩).2.1
  · obtain ⟨_,_,num⟩ := round
    have cnt := loop 2 rfl
    change n (nE L g false) = u+1 at poll
    change 2*(n (nE L g false) : Int) = n .commit+2 at cnt
    rw [poll] at cnt
    change n .commit = 2+2*wRn v.su.r28+0 at num
    have neg := (last rfl).2
    rw [gap] at neg
    cases short
    · exact False.elim ((by decide : ¬ sv (i32 0)<0) neg)
    · rw [warmRounds_eq r31,show u=1+wRn v.su.r28 by omega]
      rw [last_word q _ v.rnd]
      exact last_cols q (wRn v.su.r28) (Nat.lt_succ_of_le (wRn_le _))

end PTX.Kernels.TmlFa4Fwd.Proof.Loader

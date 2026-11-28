-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.Regs
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Lemmas.Flow.TcDataLen
import Lemmas.Flow.TcLdLen
import Lemmas.Flow.NotBulk

/-! # What a `tcgen05.ld` or `tcgen05.st` event shows

The kernel's loads and stores are the `16x32bx2` forms of the four sites: the softmax warps load
the score buffer of the round's parity (pc 1265), store the probabilities (pc 1009), load and store
the accumulator (pc 2260, 2328), and the epilogue loads it (pc 2607). The address is the buffer's
column plus the lane field `k 2^21` of the warp's broadcast word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Proof

private def plain : TcShape → Bool
  | .packed16 _ => false
  | _ => true

private def ldLens (pcs : List Nat) (n : Nat) : Bool := pcs.all fun p =>
  match kernel.code[p]? with
  | some ins => match ins.op with
    | .tcLd ds _ sh red => ds.length == n && red.isNone && plain sh
    | _ => false
  | none => false

private def stLens (pcs : List Nat) (n : Nat) : Bool := pcs.all fun p =>
  match kernel.code[p]? with
  | some ins => match ins.op with
    | .tcSt _ ss sh => ss.length == n && plain sh
    | _ => false
  | none => false

private theorem ld64 : ldLens [1265,2260,2607] 64 = true := by decide +kernel
private theorem st64 : stLens [2328] 64 = true := by decide +kernel
private theorem st32 : stLens [1009] 32 = true := by decide +kernel

private theorem plain_iff {sh : TcShape} (h : plain sh = true) : ∀ s, sh ≠ .packed16 s := by
  intro s hs
  subst hs
  cases h

private theorem ld_len {pc n : Nat} {pcs : List Nat} (hl : ldLens pcs n = true) (hpc : pc ∈ pcs)
    {ins : Instr} {ds ta sh red} (code : kernel.code[pc]? = some ins)
    (op : ins.op = .tcLd ds ta sh red) : ds.length = n ∧ red = none ∧ ∀ s, sh ≠ .packed16 s := by
  have h := List.all_eq_true.mp hl pc hpc
  rw [code] at h
  simp only [op, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1,h.1.2,plain_iff h.2⟩

private theorem st_len {pc n : Nat} {pcs : List Nat} (hl : stLens pcs n = true) (hpc : pc ∈ pcs)
    {ins : Instr} {ta ss sh} (code : kernel.code[pc]? = some ins)
    (op : ins.op = .tcSt ta ss sh) : ss.length = n ∧ ∀ s, sh ≠ .packed16 s := by
  have h := List.all_eq_true.mp hl pc hpc
  rw [code] at h
  simp only [op, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1,plain_iff h.2⟩

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat}

/-- **The shape of a load event.** -/
public theorem ld_static (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {pc a vals sh}
    (he : X.get (g,j) = some ⟨pc,.tc (.ld a vals sh)⟩) :
    ∃ i k, k < 4 ∧ ((pc = 1265 ∧ a = i%2*128 + k*2^21) ∨
        ((pc = 2260 ∨ pc = 2607) ∧ a = 256 + k*2^21)) ∧ sh = .s16x32bx2 64 ∧ vals.length = 64 := by
  obtain ⟨i,w,-,-,eq⟩ := Export.tc_operand hp hX hf base he (by rfl)
  simp only [tcStatic] at eq
  unfold Lib.opStatic Lib.bcastOffset at eq
  have lens := get_tcLd_len (by rw [hp.block]) hX he (a := a) (vals := vals) (sh := sh) rfl
  obtain ⟨ins,ds,ta,sh',red,code,op,len⟩ := lens
  refine ⟨i,(Lib.word w).toNat % 4,Nat.mod_lt _ (by norm_num),?_⟩
  have len64 : pc = 1265 ∨ pc = 2260 ∨ pc = 2607 → vals.length = 64 := fun hpc => by
    obtain ⟨n,hr,hs⟩ := ld_len ld64 (by simpa using hpc) code op
    exact (len hr hs).trans n
  split_ifs at eq
  all_goals obtain ⟨rfl,-,rfl⟩ := TcKind.ld.inj eq
  · exact ⟨.inl ⟨by omega,rfl⟩,rfl,len64 (by omega)⟩
  · exact ⟨.inr ⟨.inl (by omega),rfl⟩,rfl,len64 (by omega)⟩
  · exact ⟨.inr ⟨.inr (by omega),rfl⟩,rfl,len64 (by omega)⟩

/-- **The shape of a store event.** -/
public theorem st_static (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {pc a vals sh}
    (he : X.get (g,j) = some ⟨pc,.tc (.st a vals sh)⟩) :
    ∃ i k, k < 4 ∧ ((pc = 2328 ∧ a = 256 + k*2^21 ∧ sh = .s16x32bx2 64 ∧ vals.length = 64) ∨
      (pc = 1009 ∧ a = i%2*128 + k*2^21 ∧ sh = .s16x32bx2 32 ∧ vals.length = 32)) := by
  obtain ⟨i,w,-,-,eq⟩ := Export.tc_operand hp hX hf base he (by rfl)
  simp only [tcStatic] at eq
  unfold Lib.opStatic Lib.bcastOffset at eq
  have shapeOk : ∀ s, sh ≠ .packed16 s := by
    intro s hs
    subst hs
    split_ifs at eq <;> cases eq
  obtain ⟨ins,ta,ss,sh',code,op,len⟩ := get_tcSt_lenAny hX he (a := a) (vals := vals) rfl shapeOk
  have l64 : pc = 2328 → vals.length = 64 := fun h => by
    have := (st_len st64 (by simp [h]) code op).1
    omega
  have l32 : pc = 1009 → vals.length = 32 := fun h => by
    have := (st_len st32 (by simp [h]) code op).1
    omega
  refine ⟨i,(Lib.word w).toNat % 4,Nat.mod_lt _ (by norm_num),?_⟩
  split_ifs at eq
  all_goals obtain ⟨rfl,-,rfl⟩ := TcKind.st.inj eq
  · exact .inl ⟨by omega,rfl,rfl,l64 (by omega)⟩
  · exact .inr ⟨by omega,rfl,rfl,l32 (by omega)⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem

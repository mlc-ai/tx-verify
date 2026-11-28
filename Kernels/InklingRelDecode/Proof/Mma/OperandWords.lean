-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.OperandLayout
import Kernels.InklingRelDecode.Flow.Code
import Lemmas.Flow.Step.TcDesc
import Lemmas.Flow.Step.TcFields
import Lemmas.Flow.TcTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

def masks : List Opnd := List.replicate 4 (.imm 0)

def qOp (j : Fin 8) := TcMmaInstr.dense .one false .f16 547
  (.smem (.reg (2027+2*j.val))) (.reg (2028+2*j.val)) (.reg 548) masks
  (.reg (if j.val=0 then 9 else 11))

def vOp (j : Fin 8) := TcMmaInstr.dense .one false .f16 564
  (.tmem 565 (8*j.val : Nat)) (.reg (2044+j.val)) (.reg 566) masks
  (.reg (if j.val=0 then 14 else 16))

theorem qcode (j : Fin 8) :
    kernel.code[qkPc j]?=some ⟨some (10,false),.tcMma (qOp j)⟩ := by
  fin_cases j
  · exact Flow.code_mma_0
  · exact Flow.code_mma_1
  · exact Flow.code_mma_2
  · exact Flow.code_mma_3
  · exact Flow.code_mma_4
  · exact Flow.code_mma_5
  · exact Flow.code_mma_6
  · exact Flow.code_mma_7

theorem vcode (j : Fin 8) :
    kernel.code[pvPc j]?=some ⟨some (15,false),.tcMma (vOp j)⟩ := by
  fin_cases j
  · exact Flow.code_mma_8
  · exact Flow.code_mma_9
  · exact Flow.code_mma_10
  · exact Flow.code_mma_11
  · exact Flow.code_mma_12
  · exact Flow.code_mma_13
  · exact Flow.code_mma_14
  · exact Flow.code_mma_15

def qWord (L : Launch) (j : Fin 8) := qLo L + (2*(j.val%4)+512*(j.val/4))
def kWord (L : Launch) (i : Nat) (j : Fin 8) := kLo L (i%3) + (2*(j.val%4)+1024*(j.val/4))
def vWord (L : Launch) (i : Nat) (j : Fin 8) := vLo L ((i-1)%3)+128*j.val

variable {Q : Params} {L : Launch} {m : Mem0} {g i dst : Nat} {regs : Nat → Value} {w v : Value}
  {t : TState} {ins : Instr} {o : Option TState} {s : TcMma.OperandSpec} {b : Bool} {ms : List Nat}

private theorem reg {d : D} {r} (ht : (code L g regs w).AtD d t) (key : r ∈ Flow.live d.site.pc) :
    t.regs r=some (valueOf L regs w d r) := by
  obtain ⟨_,_,_,_,holds⟩ := ht
  exact holds_mem holds (mem_factsFrom key)

theorem q_operands (hp : Pre Q L m) (j : Fin 8) (ht : (code L g regs w).AtD ⟨.qk j,i,v⟩ t)
    (hc : kernel.code[qkPc j]?=some ins)
    (hf : Fires (qkPc j) (eventTmpl Assumptions.all L g t ins.op)
      ⟨qkPc j,.tc (.mma dst s b ms)⟩ o) :
    s.descriptor=Lib.qkDesc ∧ s.aTmem=none ∧
      s.a=⟨qWord L j*16,0,1024,0,false,false,.b128⟩ ∧
      s.b=⟨kWord L i j*16,0,1024,0,false,false,.b128⟩ ∧
      ∃ ctas, L.ctaGroup (g/L.block) .one=some ctas ∧
        ctas.head?=some s.lowCta ∧ ctas.getLast?=some s.highCta := by
  obtain rfl := Option.some.inj (hc.symm.trans (qcode j))
  have keys : ∀ j : Fin 8, let live := Flow.live (qkPc j)
      2027+2*j.val ∈ live ∧ 2028+2*j.val ∈ live ∧ 548 ∈ live := by decide +kernel
  have hA := reg ht (keys j).1
  have hB := reg ht (keys j).2.1
  have hI := reg ht (keys j).2.2
  have vals (j : Fin 8) : let val := valueOf L regs w ⟨.qk j,i,v⟩
      val (2027+2*j.val)=desc (qWord L j) ∧ val (2028+2*j.val)=desc (kWord L i j) := by
    fin_cases j <;> exact ⟨rfl,rfl⟩
  rw [(vals j).1] at hA
  rw [(vals j).2] at hB
  change t.regs 548=some (b32 qkIdesc) at hI
  have room := hp.sharedRange
  change L.sharedBase+213340≤2^18 at room
  have jq := j.isLt
  have qa : qWord L j < 2^15 := by dsimp [qWord,qLo]; omega
  have kb : kWord L i j < 2^15 := by dsimp [kWord,kLo]; omega
  have layout := issue_layout (ins := qOp j) rfl (readBits_b32 hI (by decide))
    (d := Lib.qkDesc) (by change TcMma.decode .one false .f16 qkIdesc=_; decide +kernel) hf
  have ra := readBits_b64 (L := L) (g := g) hA (by unfold descHi; omega)
  have rb := readBits_b64 (L := L) (g := g) hB (by unfold descHi; omega)
  obtain ⟨da,db⟩ := fires_tcMmaSmem_desc (m := qOp j) rfl rfl ra rb hf rfl
  rw [toNat_ofNat_lt (by unfold descHi; omega),Lib.decode_k qa] at da
  rw [toNat_ofNat_lt (by unfold descHi; omega),Lib.decode_k kb] at db
  obtain ⟨desc,noA,ctas,grp,lo,hi⟩ := layout
  exact ⟨desc,Option.isNone_iff_eq_none.mp noA,
    (Option.some.inj da).symm,(Option.some.inj db).symm,ctas,grp,lo,hi⟩

theorem v_operands (hp : Pre Q L m) (j : Fin 8) (ht : (code L g regs w).AtD ⟨.pv j,i,v⟩ t)
    (hc : kernel.code[pvPc j]?=some ins)
    (hf : Fires (pvPc j) (eventTmpl Assumptions.all L g t ins.op)
      ⟨pvPc j,.tc (.mma dst s b ms)⟩ o) :
    s.descriptor=Lib.pvDesc ∧ (∃ addr, s.aTmem=some addr) ∧ s.a=s.b ∧
      s.b=⟨vWord L i j*16,16384,1024,0,false,false,.b128⟩ ∧
      ∃ ctas, L.ctaGroup (g/L.block) .one=some ctas ∧
        ctas.head?=some s.lowCta ∧ ctas.getLast?=some s.highCta := by
  obtain rfl := Option.some.inj (hc.symm.trans (vcode j))
  have keys : ∀ j : Fin 8, 2044+j.val ∈ Flow.live (pvPc j) ∧ 566 ∈ Flow.live (pvPc j) :=
    by decide +kernel
  have hB := reg ht (keys j).1
  have hI := reg ht (keys j).2
  have val (j : Fin 8) : valueOf L regs w ⟨.pv j,i,v⟩ (2044+j.val)=vdesc (vWord L i j) := by
    fin_cases j <;> rfl
  rw [val] at hB
  change t.regs 566=some (b32 pvIdesc) at hI
  have room := hp.sharedRange
  change L.sharedBase+213340≤2^18 at room
  have jq := j.isLt
  have vb : vWord L i j < 2^15 := by dsimp [vWord,vLo]; omega
  have layout := issue_layout (ins := vOp j) rfl (readBits_b32 hI (by decide))
    (d := Lib.pvDesc) (by change TcMma.decode .one false .f16 pvIdesc=_; decide +kernel) hf
  have rb := readBits_b64 (L := L) (g := g) hB (by unfold descHi; omega)
  obtain ⟨da,db⟩ := fires_tcMmaTmem_desc (m := vOp j) rfl rfl rb hf rfl
  have same : s.a=s.b := Option.some.inj (da.symm.trans db)
  rw [toNat_ofNat_lt (by unfold descHi; omega),Lib.decode_v vb] at db
  obtain ⟨desc,noA,ctas,grp,lo,hi⟩ := layout
  refine ⟨desc,?_,same,(Option.some.inj db).symm,ctas,grp,lo,hi⟩
  cases eq : s.aTmem with
  | some a => exact ⟨a,rfl⟩
  | none => simp [eq,vOp,TcMmaInstr.dense] at noA

private theorem zero_masks (L : Launch) (g : Nat) (t : TState) :
    masks.mapM (readBits L g t 32) = .ok [0,0,0,0] := rfl

/-- **The QK issue's destination column**: the base word's column plus the parity buffer. -/
theorem q_dst (hw : w=b32 0) (j : Fin 8) (ht : (code L g regs w).AtD ⟨.qk j,i,v⟩ t)
    (hc : kernel.code[qkPc j]?=some ins)
    (hf : Fires (qkPc j) (eventTmpl Assumptions.all L g t ins.op)
      ⟨qkPc j,.tc (.mma dst s b ms)⟩ o) :
    dst=128*(i%2) ∧ ms=[0,0,0,0] ∧ b=decide (j.val≠0) := by
  obtain rfl := Option.some.inj (hc.symm.trans (qcode j))
  have keys : ∀ j : Fin 8, let live := Flow.live (qkPc j)
      547 ∈ live ∧ 548 ∈ live ∧ (if j.val=0 then 9 else 11) ∈ live := by decide +kernel
  have hD := reg ht (keys j).1
  have hI := reg ht (keys j).2.1
  have hE := reg ht (keys j).2.2
  have small : 128*(i%2) < 2^32 := by have := Nat.mod_lt i (show 0<2 by decide); omega
  have hq : valueOf L regs w ⟨.qk j,i,v⟩ 547=b32 ((0+128*(i%2))%2^32) := by subst hw; rfl
  have enable : valueOf L regs w ⟨.qk j,i,v⟩ (if j.val=0 then 9 else 11)
      =.pred (decide (j.val≠0)) := by
    fin_cases j <;> rfl
  rw [hq,Nat.zero_add,Nat.mod_eq_of_lt small] at hD
  rw [enable] at hE
  change t.regs 548=some (b32 qkIdesc) at hI
  have hd := readBits_b32 (L := L) (g := g) hD small
  have hi := readBits_b32 (L := L) (g := g) hI (by decide)
  have fields := fires_tcMmaSmem_fields (m := qOp j) (L := L) (g := g) rfl rfl rfl hd hi
    (zero_masks L g t) (mmaEnable_of hE) hf
  rcases fields with ⟨s',k,-⟩|⟨f,k⟩
  · simp only [Kind.tc.injEq,TcKind.mma.injEq] at k
    obtain ⟨rfl,-,hacc,rfl⟩ := k
    exact ⟨toNat_ofNat_lt (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by decide))),
      by simp,hacc⟩
  · simp at k

/-- **The PV issue's destination and A columns**: the O accumulator at column 256, and the A
operand at the parity buffer plus eight columns per issue. -/
theorem v_dst (hw : w=b32 0) (j : Fin 8) (ht : (code L g regs w).AtD ⟨.pv j,i,v⟩ t)
    (hc : kernel.code[pvPc j]?=some ins)
    (hf : Fires (pvPc j) (eventTmpl Assumptions.all L g t ins.op)
      ⟨pvPc j,.tc (.mma dst s b ms)⟩ o) :
    dst=256 ∧ s.aTmem=some (128*((i-1)%2)+8*j.val) ∧ ms=[0,0,0,0] ∧
      b=(if j.val=0 then decide (i≠1) else true) := by
  obtain rfl := Option.some.inj (hc.symm.trans (vcode j))
  have keys : ∀ j : Fin 8, let live := Flow.live (pvPc j)
      564 ∈ live ∧ 565 ∈ live ∧ 566 ∈ live ∧ (if j.val=0 then 14 else 16) ∈ live := by
    decide +kernel
  obtain ⟨kD,kA,kI,kE⟩ := keys j
  have hD := reg ht kD
  have hA := reg ht kA
  have hI := reg ht kI
  have hE := reg ht kE
  have small : 128*((i-1)%2) < 2^32 := by have := Nat.mod_lt (i-1) (show 0<2 by decide); omega
  have hq : valueOf L regs w ⟨.pv j,i,v⟩ 564=b32 ((0+256)%2^32) := by subst hw; rfl
  have ha : valueOf L regs w ⟨.pv j,i,v⟩ 565=b32 ((0+128*((i-1)%2))%2^32) := by subst hw; rfl
  have enable : valueOf L regs w ⟨.pv j,i,v⟩ (if j.val=0 then 14 else 16)
      =.pred (if j.val=0 then decide (i≠1) else true) := by
    fin_cases j <;> rfl
  rw [hq] at hD
  rw [ha,Nat.zero_add,Nat.mod_eq_of_lt small] at hA
  rw [enable] at hE
  change t.regs 566=some (b32 pvIdesc) at hI
  have hd := readBits_b32 (L := L) (g := g) hD (by decide)
  have hav := readBits_b32 (L := L) (g := g) hA small
  have hi := readBits_b32 (L := L) (g := g) hI (by decide)
  have off : tmemOffset (BitVec.ofNat 64 (128*((i-1)%2))).toNat (8*j.val : Nat)
      = .ok (128*((i-1)%2)+8*j.val) := by
    rw [toNat_ofNat_lt (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by decide)))]
    apply tmemOffset_of
    have := Nat.mod_lt (i-1) (show 0<2 by decide)
    have := j.isLt
    omega
  have fields := fires_tcMmaTmem_fields (m := vOp j) (L := L) (g := g) rfl rfl rfl hd hav
    (by exact_mod_cast off) hi (zero_masks L g t) (mmaEnable_of hE) hf
  rcases fields with ⟨s',k,hA',-⟩|⟨f,k⟩
  · simp only [Kind.tc.injEq,TcKind.mma.injEq] at k
    obtain ⟨rfl,rfl,hacc,rfl⟩ := k
    exact ⟨toNat_ofNat_lt (by decide),hA',by simp,hacc⟩
  · simp at k

end PTX.Kernels.InklingRelDecode.Proof.Mma

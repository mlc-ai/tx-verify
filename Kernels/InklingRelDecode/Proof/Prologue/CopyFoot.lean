-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.ShapeCopy
public import Kernels.InklingRelDecode.Proof.Lib.KvFoot
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Kernels.InklingRelDecode.Proof.Iface.PreloadBox
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Flow.TensorStoreOrigin
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Control Arith32

private def dstReg (b : Fin 3) (j : Fin 4) :=
  ([[682,685,688,690],[702,705,708,710],[724,727,730,732]][b.val]!)[j.val]!

private theorem packet (b : Fin 3) (j : Fin 4) :
    ∃ guard coords, kernel.code[(Site.ptc b j).pc]?=some ⟨guard,
      .cpTensor false false (dstReg b j) 0 (.reg 1949) coords (613+2*b.val) 0 none .tile⟩ := by
  fin_cases b <;> fin_cases j
  · exact ⟨_,_,Flow.code_211⟩
  · exact ⟨_,_,Flow.code_217⟩
  · exact ⟨_,_,Flow.code_226⟩
  · exact ⟨_,_,Flow.code_231⟩
  · exact ⟨_,_,Flow.code_253⟩
  · exact ⟨_,_,Flow.code_259⟩
  · exact ⟨_,_,Flow.code_268⟩
  · exact ⟨_,_,Flow.code_273⟩
  · exact ⟨_,_,Flow.code_295⟩
  · exact ⟨_,_,Flow.code_301⟩
  · exact ⟨_,_,Flow.code_310⟩
  · exact ⟨_,_,Flow.code_315⟩

private theorem dst_word {Q L m g w d} (hp : Pre Q L m) (b : Fin 3) (j : Fin 4) :
    valueOf Q L g w d (dstReg b j)=
      .bits 32 (addi (copyBase L d.broadcast) (copyOffset b j : Int)) := by
  fin_cases b <;> fin_cases j
  · change Value.bits 32 (copyBase L d.broadcast)=.bits 32 (addi (copyBase L d.broadcast) 0)
    rw [copy_base_value d.broadcast hp.sharedRange]
    have small : L.sharedBase+213340≤2^18 := hp.sharedRange
    nf_simp [addi,add32,r32,i32]
    omega
  all_goals rfl

/-- All preload boxes fit inside the K/V ring for either broadcast half,
including when the recorded address and source coordinate data are arbitrary. -/
theorem preload_footprint {Q L m g w d t ins e o addr sp} (hp : Pre Q L m)
    (ht : (code Q L g w).AtD d t) (b : Fin 3) (j : Fin 4) (site : d.site=.ptc b j)
    (hc : kernel.code[d.site.pc]?=some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (he : e.kind=.tensorIssue addr sp) :
    (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ ∧
    (∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
      L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608) ∧
    (∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
      l.cta=g/L.block ∧ Iface.InSlot L b.val l.addr) ∧
    (∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
      L.sharedBase+16384*((Lib.word d.broadcast).toNat%2)+Iface.preloadOff d.site.pc ≤ l.addr ∧
      l.addr<L.sharedBase+16384*((Lib.word d.broadcast).toNat%2)+Iface.preloadOff d.site.pc
        +8192) ∧
    sp.sharedBase = ⟨.shared,g/L.block,
      L.sharedBase+16384*((Lib.word d.broadcast).toNat%2)+Iface.preloadOff d.site.pc⟩ := by
  obtain ⟨guard,coords,get⟩ := packet b j
  rw [site] at hc
  obtain rfl := Option.some.inj (hc.symm.trans get)
  have keys : ∀ b j, dstReg b j ∈ ctlLive (Site.ptc b j).pc ∧
      1949 ∈ ctlLive (Site.ptc b j).pc := by decide +kernel
  obtain ⟨_,_,_,_,regs⟩ := ht
  have reg := holds_mem regs (mem_factsFrom (val := valueOf Q L g w d) (site ▸ (keys b j).1))
  rw [dst_word hp b j] at reg
  let dst := addi (copyBase L d.broadcast) (copyOffset b j : Int)
  have word : dst=BitVec.ofNat 64 dst.toNat := by simp
  change t.regs _=some (.bits 32 dst) at reg
  rw [word] at reg
  have range := copy_interval d.broadcast b j hp.sharedRange
  change L.sharedBase≤dst.toNat ∧ dst.toNat+8192≤L.sharedBase+196608 at range
  have room : L.sharedBase+213340≤2^18 := hp.sharedRange
  have issue := fires_cpTensor_copy hf he
  have loc := Except.ok.inj ((tensorLoadCopy_box issue).1.symm.trans
    (sharedEffAddr_b32 (L := L) (g := g) (x := dst.toNat) reg (by omega)))
  obtain ⟨map,_,_,bind,_,spec,_⟩ := tensorLoadCopy_ok issue
  have ptr : t.regs 1949=some (.ptr 64 true (.param (param "1")) 0) :=
    holds_mem regs (mem_factsFrom (site ▸ (keys b j).2))
  obtain ⟨_,obj⟩ := tensorMapAddress_param ptr map
  obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj (obj.symm.trans hp.paramKv))
  have descriptor : (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ := by
    rw [spec]
    exact Option.some.inj (bind.symm.trans hp.mapKvBind)
  have slot : (L.sharedBase+32768*b.val≤dst.toNat ∧
      dst.toNat+8192≤L.sharedBase+32768*(b.val+1)) ∨
      (L.sharedBase+98304+32768*b.val≤dst.toNat ∧
        dst.toNat+8192≤L.sharedBase+98304+32768*(b.val+1)) :=
    copy_slot_interval (L := L) d.broadcast b j room
  have value := copy_dest_value (L := L) d.broadcast b j room
  have off : copyOffset b j = Iface.preloadOff d.site.pc := by
    rw [site]; fin_cases b <;> fin_cases j <;> rfl
  refine ⟨descriptor,?_,?_,?_,?_⟩
  · intro x y z l byte
    obtain ⟨_,_,lo,hi⟩ := Lib.map_foot (Q := Q) descriptor byte
    rw [loc] at lo hi
    dsimp only at lo hi
    omega
  · intro x y z l byte
    obtain ⟨_,cta,lo,hi⟩ := Lib.map_foot (Q := Q) descriptor byte
    rw [loc] at lo hi cta
    dsimp only at lo hi cta
    refine ⟨cta,?_⟩
    unfold Iface.InSlot
    omega
  · intro x y z l byte
    obtain ⟨_,_,lo,hi⟩ := Lib.map_foot (Q := Q) descriptor byte
    rw [loc] at lo hi
    dsimp only at lo hi
    rw [value, off] at lo hi
    omega
  · rw [loc, value, off]

end PTX.Kernels.InklingRelDecode.Proof.Prologue

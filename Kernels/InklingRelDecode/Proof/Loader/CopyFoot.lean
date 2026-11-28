-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.CopyShape
public import Kernels.InklingRelDecode.Proof.Lib.KvFoot
public import Kernels.InklingRelDecode.Proof.Iface.Regions
import Kernels.InklingRelDecode.Proof.Loader.TileRing
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Flow.TensorStoreOrigin

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

private def dstReg (p : Fin 4) (half : Bool) :=
  (if half then [585,589,594,596] else [582,587,592,595])[p.val]!

def boxOffset (p : Fin 4) (half : Bool) :=
  (if half then [16384,114688,24576,122880] else [0,98304,8192,106496])[p.val]!

private theorem fetch (p : Fin 4) (half : Bool) :
    ∃ guard coords, kernel.code[(Site.copy p half).pc]? = some ⟨guard,
      .cpTensor false false (dstReg p half) 0 (.reg 1949) coords 580 0 none .tile⟩ := by
  fin_cases p <;> cases half
  · exact ⟨_,_,Flow.code_2389⟩
  · exact ⟨_,_,Flow.code_2391⟩
  · exact ⟨_,_,Flow.code_2394⟩
  · exact ⟨_,_,Flow.code_2396⟩
  · exact ⟨_,_,Flow.code_2404⟩
  · exact ⟨_,_,Flow.code_2406⟩
  · exact ⟨_,_,Flow.code_2410⟩
  · exact ⟨_,_,Flow.code_2412⟩

private noncomputable def tile (L : Launch) (i : Value) :=
  add32 (r32 (BitVec.ofNat 64 L.sharedBase)) (mad32 (quotient (bits i)) (i32 (-98304))
    (shl (bits i) 15))

private theorem add_zero_tile (L : Launch) (i : Value) : addi (tile L i) 0 = tile L i := by
  have key (v : BitVec 64) : addi (r32 v) 0 = r32 v := by
    rw [show v=BitVec.ofNat 64 v.toNat by simp]
    nf_simp [addi,add32,r32,i32]
    omega
  exact key _

private theorem register (L : Launch) (g : Nat) (w i n a b : Value) (regs : Nat → Value)
    (p : Fin 4) (half : Bool) :
    valueOf L g w regs ⟨.copy p half,i,n,a,b⟩ (dstReg p half) =
      .bits 32 (addi (tile L i) (boxOffset p half : Int)) := by
  fin_cases p <;> cases half
  · exact congrArg (Value.bits 32) (add_zero_tile L i).symm
  all_goals rfl

private theorem boxOffset_split (p : Fin 4) (half : Bool) :
    boxOffset p half ≤ 24576 ∨ 98304 ≤ boxOffset p half := by
  fin_cases p <;> cases half <;> decide

/-- Each of the eight transfers misses the count and role words for every
possible signed counter and every source coordinate. -/
theorem copy_footprint {Q L m g w regs i n a b p half t ins e o addr sp}
    (hp : Pre Q L m) (hr : regs 1949 = .ptr 64 true (.param (param "1")) 0)
    (ht : (code L g w regs).AtD ⟨.copy p half,i,n,a,b⟩ t)
    (hc : kernel.code[(Site.copy p half).pc]? = some ins)
    (hf : Fires (Site.copy p half).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (he : e.kind=.tensorIssue addr sp) :
    (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ ∧
    (∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
      l.addr<L.sharedBase+196608 ∨ L.sharedBase+213340≤l.addr) ∧
    ((bits i).toNat<2^31 → ∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
      l.cta=g/L.block ∧ Iface.InSlot L ((bits i).toNat%3) l.addr ∧
        L.sharedBase+32768*((bits i).toNat%3)+boxOffset p half ≤ l.addr ∧
        l.addr < L.sharedBase+32768*((bits i).toNat%3)+boxOffset p half+8192) ∧
    ((bits i).toNat<2^31 → sp.sharedBase =
      ⟨.shared,g/L.block,L.sharedBase+32768*((bits i).toNat%3)+boxOffset p half⟩) := by
  obtain ⟨guard,coords,get⟩ := fetch p half
  obtain rfl := Option.some.inj (hc.symm.trans get)
  obtain ⟨_,_,_,_,hregs⟩ := ht
  have live : ∀ p half, dstReg p half ∈ Flow.live (Site.copy p half).pc ∧
      1949 ∈ Flow.live (Site.copy p half).pc ∧ boxOffset p half ≤ 122880 := by decide +kernel
  obtain ⟨hd,hm,bound⟩ := live p half
  have dest := holds_mem hregs (mem_factsFrom hd)
  rw [register] at dest
  let dst := addi (tile L i) (boxOffset p half : Int)
  have dword : dst = BitVec.ofNat 64 dst.toNat := by simp
  change t.regs _=some (.bits 32 dst) at dest
  rw [dword] at dest
  have low : dst.toNat<2^32 := by
    change (truncBits 32 _).toNat<2^32
    simp only [truncBits,BitVec.toNat_ofNat]; omega
  have issue := fires_cpTensor_copy hf he
  have location := Except.ok.inj ((tensorLoadCopy_box issue).1.symm.trans (sharedEffAddr_b32
    (L := L) (g := g) (x := dst.toNat) dest low))
  obtain ⟨map,_,_,bind,_,spec,_⟩ := tensorLoadCopy_ok issue
  have ptr := holds_mem hregs (mem_factsFrom hm)
  change t.regs 1949=some (regs 1949) at ptr
  rw [hr] at ptr
  obtain ⟨_,obj⟩ := tensorMapAddress_param ptr map
  obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj (obj.symm.trans hp.paramKv))
  have descriptor : (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ := by
    rw [spec]
    exact Option.some.inj (bind.symm.trans hp.mapKvBind)
  refine ⟨descriptor,?_,?_,?_⟩
  · intro x y z l byte
    obtain ⟨_,_,lo,hi⟩ := Lib.map_foot (Q := Q) descriptor byte
    rw [location] at lo hi
    have apart := tile_separate L (bits i) _ bound hp.sharedRange
    change dst.toNat+8192≤_ ∨ _≤dst.toNat at apart
    dsimp only at lo hi
    omega
  · intro small x y z l byte
    obtain ⟨_,cta,lo,hi⟩ := Lib.map_foot (Q := Q) descriptor byte
    rw [location] at lo hi cta
    have where_ := tile_slot L (bits i) _ bound hp.sharedRange small
    change dst.toNat=_ at where_
    dsimp only at lo hi cta
    refine ⟨cta,?_,by omega,by omega⟩
    have split := boxOffset_split p half
    unfold Iface.InSlot
    omega
  · intro small
    rw [location]
    exact congrArg (Loc.mk .shared (g/L.block)) (tile_slot L (bits i) _ bound hp.sharedRange small)

end PTX.Kernels.InklingRelDecode.Proof.Loader

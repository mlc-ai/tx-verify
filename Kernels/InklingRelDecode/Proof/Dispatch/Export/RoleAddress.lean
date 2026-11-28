-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Gen.StepDispatch
import Lemmas.Flow.LoadShared
import Lemmas.Flow.Final

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch.Export
open PTX PTX.Proof PTX.Flow

private def roleLoad : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 8,
    ext := .zero 32, addr := ⟨.reg 536 32,213332⟩, dsts := [some 535] }

private theorem access {A L g t o a bs v}
    (reg : t.regs 536=some (b32 v)) (small : v+213332<2^32) (sub : t.sub=0)
    (fire : Fires 2340 (eventTmpl A L g t (.mem roleLoad)) ⟨2340,.rd a bs⟩ o) :
    a.loc=⟨.shared,g/L.block,v+213332⟩ ∧ a.size=1 := by
  have rule : roleLoad.rule=some .threadAccess := rfl
  have space : roleLoad.locSpace?=none := rfl
  have bits := readBits_b32 (L := L) (g := g) reg (show v<2^32 by omega)
  have wrap : wrapAddr 32 (BitVec.ofNat 64 v) 213332=v+213332 := by
    simp only [wrapAddr,BitVec.ofInt_ofNat,truncBits,BitVec.toNat_ofNat,BitVec.toNat_add]
    omega
  have bound : v % 2^64 < 2^32 := by omega
  simp only [eventTmpl,memTmpl,rule,space,accessTmpl] at fire
  rw [accessAcc_of_weak (a := roleLoad) rfl] at fire
  simp only [roleLoad,accessLoc,
    readReg,reg,b32,bits,bind,Except.bind,pure,Except.pure,BitVec.toNat_ofNat,bound,wrap,elemAcc,
    sub,Loc.at,DType.width] at fire
  simp only [↓reduceIte,show (false || ({ } : CacheHints).globalOnly || 1 == 8 ||
    1 == 4 && 8 == 64)=false by decide,Bool.false_and,Bool.false_eq_true] at fire
  simp only [Nat.reduceDiv,Nat.mul_one,Nat.mod_one,show ¬(1=0 ∨ (0:Nat)≠0) by decide,
    ↓reduceIte] at fire
  obtain ⟨_,_,eq,_⟩ := fire
  cases eq
  exact ⟨rfl,rfl⟩

/-- Each worker warp reads its own byte of the role word at both dispatch rounds. -/
public theorem role_address {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨2340,.rd a bs⟩) :
    4≤g%L.block/32 ∧ g%L.block/32<8 ∧ a.size=1 ∧
    a.loc=⟨.shared,g/L.block,L.sharedBase+213336+(g%L.block/32-4)⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨w,x,r,n,rfl⟩ := (state_role s).dispatchRead pc.symm
  obtain ⟨low,rfl⟩ := worker_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  change kernel.code[2340]?=some ins at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2340)
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have reg := holds_mem regs (mem_factsFrom (show 536 ∈ Flow.live 2340 by decide))
  have room := hp.sharedRange
  change L.sharedBase+213340≤2^18 at room
  change 128≤g%L.block at low
  have high : g%L.block<256 := by rw [hp.block]; omega
  have word : valueOf L g (BitVec.ofNat 64 (g%L.block/32))
      (startRegs Q L g w (BitVec.ofNat 64 (g%L.block/32))) 536=b32 (L.sharedBase+g%L.block/32) := by
    unfold valueOf
    nf_simp
    omega
  rw [word] at reg
  change Fires 2340 (eventTmpl Assumptions.all L g t (.mem roleLoad)) _ _ at fire
  generalize Assumptions.all = A at fire
  have get := access (L := L) (g := g) (A := A) (a := a) (bs := bs) (o := o)
    reg (by omega) sub
  obtain ⟨loc,size⟩ := get fire
  refine ⟨by omega,by omega,size,?_⟩
  rw [loc]
  exact congrArg (Loc.mk .shared (g/L.block)) (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Dispatch.Export

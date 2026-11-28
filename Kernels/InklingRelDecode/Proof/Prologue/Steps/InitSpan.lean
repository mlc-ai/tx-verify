-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Pred
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
private theorem guardOp (i : Fin 12) : kernel.code[(Site.el i).pc+1]? =
    some ⟨none,.int ⟨.and,.pred,false,[some (26+i.val)],[.reg 40,.reg (41+i.val)]⟩⟩ := by
  fin_cases i <;> first | exact Flow.code_131 | exact Flow.code_136 | exact Flow.code_140 |
    exact Flow.code_144 | exact Flow.code_148 | exact Flow.code_152 | exact Flow.code_156 |
    exact Flow.code_160 | exact Flow.code_164 | exact Flow.code_168 | exact Flow.code_172 |
    exact Flow.code_176

private def addressPc (i : Fin 12) := 133+4*i.val
private theorem address (i : Fin 12) : kernel.code[addressPc i]? =
    some ⟨none,.int ⟨.add,.int .s 32,false,[some (613+i.val)],
      [.reg 666,.imm (MbarRow.initOffset i)]⟩⟩ := by
  fin_cases i <;> first | exact Flow.code_133 | exact Flow.code_137 | exact Flow.code_141 |
    exact Flow.code_145 | exact Flow.code_149 | exact Flow.code_153 | exact Flow.code_157 |
    exact Flow.code_161 | exact Flow.code_165 | exact Flow.code_169 | exact Flow.code_173 |
    exact Flow.code_177

private noncomputable def guardRegs (i : Fin 12) := (26+i.val)::ctlLive (Site.el i).pc
private noncomputable def addrRegs (i : Fin 12) := if i=0 then 666::guardRegs i else guardRegs i

private theorem guardChecked : ∀ i : Fin 12,
    (40 ∈ ctlLive (Site.el i).pc) ∧ (26+i.val ∉ ctlLive (Site.el i).pc) ∧
    Assumptions.emuSites.contains ((Site.el i).pc+1) = false := by decide +kernel

private theorem addrChecked : ∀ i : Fin 12,
    (666 ∈ addrRegs i) ∧ Assumptions.emuSites.contains (addressPc i) = false ∧
    (ctlLive (Site.init i).pc).all (fun r => decide (r=613+i.val ∨ r ∈ addrRegs i)) ∧
    MbarRow.initOffset i < 2^31 := by decide +kernel

private theorem sharedWord (base : Nat) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 (base+0))) = u32 base := by
  apply congrArg (Value.bits 32)
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits,BitVec.toNat_ofNat,Nat.add_zero]
  omega

private theorem shared {Q L g w d} :
    Seg kernel Assumptions.all L g 1 132 (factsFrom (guardRegs 0) (valueOf Q L g w d))
      133 (factsFrom (addrRegs 0) (valueOf Q L g w d)) := by
  intro t ht
  seg_fp ht using exact sharedWord _

theorem init_span {Q L g w} (d : D) (i : Fin 12) :
    SegU kernel Assumptions.all L g ((Site.el i).pc+1)
      ((41+i.val,.pred d.elected)::facts Q L g w d (Site.el i).pc)
      (Site.init i).pc (facts Q L g w d (Site.init i).pc) := by
  let V := valueOf Q L g w d
  let addr := MbarRow.initOffset i
  have pred : V (26+i.val) = .pred (decide (g%L.block<32) && d.elected) := by
    fin_cases i <;> rfl
  obtain ⟨key,fresh,hs⟩ := guardChecked i
  apply SegU.comp (b := (Site.el i).pc+1+1) (G := factsFrom (guardRegs i) V)
  · change SegU _ _ _ _ _ _ _ ((26+i.val,V (26+i.val))::facts Q L g w d (Site.el i).pc)
    rw [pred]
    apply and_vote (guardOp i) hs (mem_factsFrom (val := V) key)
    rwa [factsFrom_keys]
  · apply SegU.comp (b := addressPc i) (G := factsFrom (addrRegs i) V)
    · by_cases zero : i=0
      · subst i; exact SegU.of_seg shared
      · have eq : (Site.el i).pc+1+1 = addressPc i := by
          fin_cases i <;> first | contradiction | rfl
        rw [eq,addrRegs,ite_eq_right zero]
        exact fun t ht => .inl ⟨t,.refl,ht⟩
    · obtain ⟨base,hs,live,bound⟩ := addrChecked i
      have addrVal : V (613+i.val) = u32 (L.sharedBase + addr) := by fin_cases i <;> rfl
      change SegU _ _ _ _ _ _ _ (factsFrom (ctlLive (Site.init i).pc) V)
      have add := Lib.sum_span (L := L) (g := g) (V := V) (rs := addrRegs i)
        (rs' := ctlLive (Site.init i).pc) false bound (address i) hs base
        (addrVal.trans (Lib.addBase_bits L.sharedBase addr).symm)
        (fun _ _ => by fin_cases i <;> exact ⟨rfl,rfl⟩)
        (fun r hr => of_decide_eq_true (List.all_eq_true.mp live r hr))
      have pc : addressPc i+1 = (Site.init i).pc := by fin_cases i <;> rfl
      rwa [pc] at add

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

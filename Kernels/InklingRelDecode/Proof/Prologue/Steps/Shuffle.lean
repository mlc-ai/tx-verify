-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

def pshDest (b : Fin 3) := [693,714,736][b.val]!
theorem psh_fetch (b : Fin 3) : kernel.code[(Site.psh b).pc]? =
    some ⟨none,.warp ⟨.shfl .idx,some (.int .b 32),[some (pshDest b)],
      [.reg 464,.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
  fin_cases b
  · exact Flow.code_202
  · exact Flow.code_244
  · exact Flow.code_286

theorem psh_frames : ∀ b, (ctlLive (Site.pel b 0).pc).all fun r =>
    decide (r=pshDest b ∨ (copyReg r=false ∧ r ∈ ctlLive (Site.psh b).pc)) := by decide +kernel

/-- The broadcast selects the tensor copy's row and destination, independently of election. -/
theorem step_shuffle {Q L g w} (d : D) (b : Fin 3) (hs : d.site = .psh b) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.psh b,a,x,c,won,bcast⟩
  refine ⟨fun _ => ⟨_,psh_fetch b,rfl,trivial⟩,?_⟩
  intro t ev u ins hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (psh_fetch b))
  obtain ⟨v,i,j,recv,ok,rfl,rfl⟩ := fires_shfl (p := none) hf
  let dn : D := {d with site := .pel b 0,broadcast := recv}
  obtain ⟨hpc,sub,acc,fault,regs⟩ := hat
  have pc : d.site.pc+1=dn.site.pc := by fin_cases b <;> rfl
  let u := PTX.next (setReg t (pshDest b) recv)
  refine .inl (.inr ⟨dn,u,rfl,.refl,.inl ⟨⟨(congrArg (·+1) hpc).trans pc,sub,acc,fault,?_⟩,
    trivial⟩⟩)
  apply holds_of_pointwise
  intro r key
  have use := of_decide_eq_true (List.all_eq_true.mp (psh_frames b) r key)
  by_cases eq : r=pshDest b
  · subst r
    have val : valueOf Q L g w dn (pshDest b)=recv := by fin_cases b <;> rfl
    simp [u,PTX.next,setReg,val]
  · obtain ⟨fixed,old⟩ := use.resolve_left eq
    change Function.update t.regs (pshDest b) (some recv) r = _
    rw [Function.update_of_ne eq]
    simpa only [valueOf,fixed,Bool.false_eq_true,↓reduceIte,dn] using
      (holds_mem regs (mem_factsFrom (val := valueOf Q L g w d) old))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

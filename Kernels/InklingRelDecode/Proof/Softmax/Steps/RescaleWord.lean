-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Rescale
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Butterfly
import Kernels.InklingRelDecode.Flow.Code
import Lemmas.Flow.Step.DataLoadU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

private theorem val_word (d : D) : valueOf e L g d 1542 = d.held.word := by simp [valueOf]

private theorem val_peer (d : D) : valueOf e L g d 1543 = d.held.peer := by simp [valueOf]

theorem step_ldL : (code e L g).StepAtU ⟨.ldL,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.dataLoadU (C := code e L g) (d := ⟨.ldL,i,v⟩)
    (dn := fun bs => ⟨.shfl11,i,{v with word := Lib.loadWord bs}⟩)
    Flow.code_load_202 rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => body_inv hi rfl rfl)
  · change _ ∉ (factsFrom (ctlLive 2252) _).map Prod.fst
    rw [factsFrom_keys]
    decide +kernel
  · intro bs w h t ⟨pc,sub,acc,fault,regs⟩
    have eq : Lib.loadWord bs = w := by simp [Lib.loadWord,h]; rfl
    refine .inl ⟨t,.refl,pc,sub,acc,fault,holds_of_pointwise ?_⟩
    intro r hr
    have cover : ∀ r ∈ ctlLive 2253, r = 1542 ∨ r ∈ ctlLive 2252 := by decide +kernel
    rcases cover r hr with rfl | hm
    · rw [val_word]
      simpa [eq] using regs.1
    · have off : ∀ r ∈ ctlLive 2252, r ∉ wordRegs := by decide +kernel
      rw [val_frame (off r hm) rfl .shfl11 .ldL]
      exact holds_mem regs.2 (mem_factsFrom hm)

private theorem min_seg (w : Value) :
    SegU kernel Assumptions.all L g 2254
      ((1543,w) :: facts e L g ⟨.shfl11,i,v⟩ 2253) 2255
      (facts e L g ⟨.shfl12,i,{v with peer := w}⟩ 2255) := by
  intro t ⟨pc,sub,acc,fault,hb,regs⟩
  have ha : t.regs 1542 = some v.word :=
    (val_word (e := e) (L := L) (g := g) ⟨.shfl11,i,v⟩) ▸
      holds_mem regs (mem_factsFrom (by decide : 1542 ∈ ctlLive 2253))
  have m := word_min (L := L) (g := g) pc ha hb
  have ci : kernel.code[t.pc]? = some ⟨none,MinCore.minOp 1544 [1542,1543]⟩ :=
    pc ▸ Flow.code_2254
  cases hm : MinCore.minE [v.word,w] with
  | error f =>
    rw [hm] at m
    exact .inr (dead_of_error ci rfl fault m)
  | ok x =>
    rw [hm] at m
    have hτ := tau_of_ok ci rfl fault m
    refine .inl ⟨_,Relation.ReflTransGen.single hτ,congrArg (·+1) pc,sub,acc,fault,
      holds_of_pointwise ?_⟩
    intro r hr
    have cover : ∀ r ∈ ctlLive 2255, r = 1544 ∨ (r ∈ ctlLive 2253 ∧ r ∉ wordRegs) := by
      decide +kernel
    rcases cover r hr with rfl | ⟨hm',hw⟩
    · rw [val_min _ (by decide)]
      simp [PTX.next,setReg,Lib.minWord,hm]; rfl
    · have h3 : r ≠ 1544 := fun h => hw (by simp [wordRegs,minRegs,h])
      rw [← val_frame hw rfl .shfl11 .shfl12]
      simp only [PTX.next,setReg,Function.update_of_ne h3]
      exact holds_mem regs (mem_factsFrom hm')

theorem step_shfl11 : (code e L g).StepAtU ⟨.shfl11,i,v⟩ where
  site := fun _ => ⟨_,Flow.code_2253,rfl,trivial⟩
  step := by
    intro t ev u ins hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2253)
    obtain ⟨a,b,c,w,ok,rfl,rfl⟩ := fires_shfl (p := none) hf
    have absent : 1543 ∉ ((code e L g).facts ⟨.shfl11,i,v⟩).map Prod.fst := by
      change 1543 ∉ (factsFrom (ctlLive 2253) _).map Prod.fst
      rw [factsFrom_keys]
      decide +kernel
    have hs := At.set (r := 1543) (v := w) (Code.at_of_atD hat rfl rfl)
      (fun p h he => absent (he ▸ List.mem_map_of_mem h))
    obtain ⟨pc,sub0,acc,fault,regs⟩ := hs
    have valid : Inv e (g%L.block) ⟨.shfl12,i,{v with peer := w}⟩ := body_inv hi rfl rfl
    obtain ⟨s,steps,good⟩ := Code.landsU (C := code e L g)
      (d := ⟨.shfl12,i,{v with peer := w}⟩) (u := PTX.next (setReg t 1543 w))
      ⟨pc,sub0,acc,fault,regs⟩ (min_seg w) valid rfl rfl
    exact .inl (.inr ⟨_,s,rfl,steps,good⟩)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

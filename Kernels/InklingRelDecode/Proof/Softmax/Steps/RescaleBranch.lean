-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Rescale
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.BranchU
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

private theorem test (a b : Value) {F : List (Nat × Value)}
    (free : ∀ x ∈ F, x.1 ≠ 1546 ∧ x.1 ≠ 170) :
    SegU kernel Assumptions.all L g 2256 ((1544,a)::(1545,b)::F)
      2258 ((170,.pred (skipRescale L g a b))::F) := by
  intro t ht
  obtain ⟨pc,sub,acc,fault,ha,hb,regs⟩ := ht
  have m := rescale_min (L := L) (g := g) pc ha hb
  have ci : kernel.code[t.pc]? = some ⟨none,MinCore.minOp 1546 [1544,1545]⟩ := pc ▸ Flow.code_2256
  cases hm : MinCore.minE [a,b] with
  | error f =>
    rw [hm] at m
    exact .inr (dead_of_error ci rfl fault m)
  | ok x =>
    rw [hm] at m
    let u := PTX.next (setReg t 1546 x)
    have hτ := tau_of_ok ci rfl fault m
    have pu : u.pc = 2257 := congrArg (·+1) pc
    have c := rescale_cmp (L := L) (g := g) (t := u) (m := x) pu (by simp [u,PTX.next,setReg])
    have cj : kernel.code[u.pc]? = some ⟨none,rescaleCmp⟩ := pu ▸ Flow.code_2257
    cases hq : setpE (.unord .ge) false x (b32 1065353216) with
    | error f =>
      rw [hq] at c
      exact .inr (Machine.dead_of_tau hτ (dead_of_error cj rfl fault c))
    | ok q =>
      rw [hq] at c
      have step := tau_of_ok cj rfl fault c
      have eq : skipRescale L g a b = q := by
        rw [skipRescale_eq,hm]
        exact congrArg (fun x : Exec Bool => x.toOption.getD false) hq
      rw [eq]
      have t1 : Tau kernel Assumptions.all L g t u := hτ
      have t2 : Tau kernel Assumptions.all L g u (PTX.next (setReg u 170 (.pred q))) := step
      refine .inl ⟨_,(Relation.ReflTransGen.single t1).tail t2,congrArg (·+1) pu,sub,acc,
        fault,?_,?_⟩
      · simp [PTX.next,setReg]
      · exact holds_update (holds_update regs fun x h => (free x h).1) fun x h => (free x h).2

private theorem after_test (q : Bool) :
    let d : D := ⟨.shfl12,i,v⟩
    let z := if q then Site.bar20 else Site.ldO
    SegU kernel Assumptions.all L g 2258 ((170,.pred q)::facts e L g d 2255)
      z.pc (facts e L g ⟨z,i,v⟩ z.pc) := by
  dsimp only
  apply (SegU.branch q Flow.code_2258 Lib.bra_rule (segFree (by decide))).comp
  cases q
  · apply Lib.sum_span true (δ := (Lib.word v.base).toNat%4*2^21) (by omega) Flow.code_2259
      (by decide) (by decide : 491 ∈ ctlLive 2255) rfl
      (fun _ h => Lib.delta_reg h (show 506 ∈ ctlLive 2255 by decide) rfl (by omega))
      (by decide +kernel : ∀ x ∈ ctlLive 2260, x = 1611 ∨ x ∈ ctlLive 2255)
  · change SegU _ _ _ _ 949 (facts e L g _ 2255) 999 (facts e L g _ 999)
    apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by decide) (by decide +kernel)
    · rw [facts,factsFrom_keys]; decide +kernel
    · exact project (p := 2255) (q := 999) (by decide +kernel)

theorem step_shfl12 : (code e L g).StepAtU ⟨.shfl12,i,v⟩ where
  site := fun _ => ⟨_,Flow.code_2255,rfl,trivial⟩
  step := by
    intro t ev u ins hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2255)
    obtain ⟨a,b,c,w,ok,rfl,rfl⟩ := fires_shfl (p := none) hf
    have ha := (Lib.shfl_operand (n := 1) rfl rfl hf rfl).1
    let q := skipRescale L g a w
    let z := if q then Site.bar20 else Site.ldO
    have valid : Inv e (g%L.block) ⟨z,i,v⟩ := by
      apply body_inv hi rfl
      dsimp [z]; split <;> rfl
    have key : ∀ x ∈ facts e L g ⟨.shfl12,i,v⟩ 2255, x.1 ∉ [1545,1546,170] := by
      intro x hx
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
      exact (by decide +kernel : ∀ r ∈ ctlLive 2255, r ∉ [1545,1546,170]) r hr
    obtain ⟨pc,sub,acc,fault,regs⟩ := hat
    have cross := (test (L := L) (g := g) a w (fun x hx => by
      have off := key x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at off
      exact off.2)).comp
      (after_test (e := e) (L := L) (g := g) (i := i) (v := v) q)
    have start : At (PTX.next (setReg t 1545 w)) 2256
        ((1544,a)::(1545,w)::facts e L g ⟨.shfl12,i,v⟩ 2255) := by
      refine ⟨congrArg (·+1) pc,sub,acc,fault,?_,?_,holds_update regs ?_⟩
      · simpa [PTX.next,setReg] using ha
      · simp [PTX.next,setReg]
      · intro x hx he
        exact key x hx (he ▸ List.mem_cons_self ..)
    obtain ⟨s,steps,good⟩ := Code.landsU (C := code e L g) (d := ⟨z,i,v⟩)
      start cross valid rfl rfl
    refine .inl (.inr ⟨⟨z,i,v⟩,s,?_,steps,good⟩)
    rfl

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

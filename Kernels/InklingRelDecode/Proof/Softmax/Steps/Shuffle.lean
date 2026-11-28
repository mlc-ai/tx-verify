-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Numeric
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

theorem shuffle_data {s z : Site} {dst src off : Nat}
    (hc : kernel.code[s.pc]? = some ⟨none,.warp ⟨.shfl .bfly,some (.int .b 32),[some dst],
      [.reg src,.imm off,.imm 31],some (.imm (-1))⟩⟩)
    (hn : ∀ ev, next e L g ⟨s,i,v⟩ ev = some (some ⟨z,i,v⟩))
    (live : SiteBody s ∧ SiteBody z) (free : dst ∉ ctlLive s.pc)
    (seg : SegU kernel Assumptions.all L g (s.pc+1) (facts e L g ⟨s,i,v⟩ s.pc)
      z.pc (facts e L g ⟨z,i,v⟩ z.pc)) : (code e L g).StepAtU ⟨s,i,v⟩ where
  site := fun _ => ⟨_,hc,rfl,trivial⟩
  step := by
    intro t ev u ins hat hi get fire
    obtain rfl := Option.some.inj (get.symm.trans hc)
    obtain ⟨a,b,c,recv,ok,rfl,rfl⟩ := fires_shfl (p := none) fire
    obtain ⟨pc,sub,acc,fault,regs⟩ := hat
    have key : dst ∉ ((code e L g).facts ⟨s,i,v⟩).map Prod.fst := by
      change dst ∉ (factsFrom _ _).map Prod.fst
      rwa [factsFrom_keys]
    obtain ⟨w,steps,good⟩ := Code.landsU (C := code e L g) (d := ⟨z,i,v⟩)
      (u := PTX.next (setReg t dst recv))
      ⟨congrArg (·+1) pc,sub,acc,fault,holds_update regs
        fun p h eq => key (eq ▸ List.mem_map_of_mem h)⟩ seg (body_inv hi live.1 live.2) rfl rfl
    exact .inl (.inr ⟨_,w,hn ⟨s.pc,.shfl .bfly a b c recv ok⟩,steps,good⟩)

theorem step_shfl5 : (code e L g).StepAtU ⟨.shfl5,i,v⟩ := by
  apply shuffle_data (s := .shfl5) (z := .shfl6) Flow.code_shfl_5 (fun _ => rfl)
    (by decide) (by decide +kernel)
  exact carry_seg (by decide +kernel) exp_to_shuffle

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

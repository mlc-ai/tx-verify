-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Kernels.InklingRelDecode.Gen.StepSoftmax10
import Kernels.InklingRelDecode.Gen.StepSoftmax39
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Lemmas.Flow.SegJump

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

private theorem st_step {s z : Site} {p ta ss sh}
    (hc : kernel.code[s.pc]? = some ⟨some (p,false),.tcSt ta ss sh⟩)
    (gd : p ∈ ctlLive s.pc) (guardVal : valueOf e L g ⟨s,i,v⟩ p = .pred true)
    (hw : Assumptions.all.any (·.tcStWaitLd s.pc) = false)
    (hn : ∀ ev, next e L g ⟨s,i,v⟩ ev = some (some ⟨z,i,v⟩))
    (live : SiteBody s ∧ SiteBody z) (pc : s.pc+1 = z.pc)
    (sub : ∀ r ∈ ctlLive z.pc, r ∈ ctlLive s.pc) : (code e L g).StepAtU ⟨s,i,v⟩ where
  site := fun _ => ⟨_,hc,rfl,Code.guardTrue_factsFrom gd guardVal⟩
  step := by
    intro t ev u ins hat hi get fire
    obtain rfl := Option.some.inj (get.symm.trans hc)
    obtain ⟨atPc,sub0,acc,fault,regs⟩ := hat
    have hp : t.pc = s.pc := atPc
    obtain rfl := fires_tcSt_next (hp ▸ hw) fire
    refine .inl (.inr ⟨_,_,hn ev,.refl,.inl ⟨⟨?_,sub0,acc,fault,?_⟩,body_inv hi live.1 live.2⟩⟩)
    · exact (congrArg (·+1) hp).trans pc
    · exact holds_factsFrom_mono regs sub

theorem step_tmemSt : (code e L g).StepAtU ⟨.tmemSt,i,v⟩ := by
  apply st_step (s := .tmemSt) (z := .tmemWait) Flow.code_tmemStore_0 (by decide +kernel)
    rfl (by decide +kernel) (fun _ => rfl) (by decide) rfl (by decide +kernel)

theorem step_stO : (code e L g).StepAtU ⟨.stO,i,v⟩ := by
  apply st_step (s := .stO) (z := .waitStO) Flow.code_tmemStore_1 (by decide +kernel)
    rfl (by decide +kernel) (fun _ => rfl) (by decide) rfl (by decide +kernel)

theorem step_bar24 : (code e L g).StepAtU ⟨.bar24,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.advanceU (C := code e L g) (d := ⟨.bar24,i,v⟩) (dn := ⟨.stO,i,v⟩)
    Flow.code_bar_24 rfl fires_barSyncN_next (fun _ => rfl) rfl rfl rfl rfl (body_inv hi rfl rfl)
  change SegU _ _ _ _ 2327 (facts e L g _ 2326) 2328 (facts e L g _ 2328)
  ink_ctl

theorem step_bar20 : (code e L g).StepAtU ⟨.bar20,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.advanceU (C := code e L g) (d := ⟨.bar20,i,v⟩) (dn := ⟨.tmemSt,i,v⟩)
    Flow.code_bar_20 rfl fires_barSyncN_next (fun _ => rfl) rfl rfl rfl rfl (body_inv hi rfl rfl)
  change SegU _ _ _ _ 1000 (facts e L g _ 999) 1009 (facts e L g _ 1009)
  ink_ctl

theorem step_waitStO : (code e L g).StepAtU ⟨.waitStO,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.advanceU (C := code e L g) (d := ⟨.waitStO,i,v⟩) (dn := ⟨.bar20,i,v⟩)
    Flow.code_tmemWait_3 rfl fires_tcWaitSt_next (fun _ => rfl)
    rfl rfl rfl rfl (body_inv hi rfl rfl)
  apply (SegU.of_seg (seg_jmp Flow.code_2330 (fun t _ => Lib.bra_rule t)
    (segFree (pc := 2330) (by decide)))).comp
  change SegU _ _ _ _ 949 (facts e L g _ 2329) 999 (facts e L g _ 999)
  apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by decide) (by decide +kernel)
  · rw [facts,factsFrom_keys]
    decide +kernel
  · exact project (p := 2329) (q := 999) (by decide +kernel)

theorem step_tmemWait : (code e L g).StepAtU ⟨.tmemWait,i,v⟩ := by
  apply step_of_inv
  intro hi
  apply Code.advanceU (C := code e L g) (d := ⟨.tmemWait,i,v⟩) (dn := ⟨.bar21,i,v⟩)
    Flow.code_tmemWait_0 rfl fires_tcWaitSt_next (fun _ => rfl)
    rfl rfl rfl rfl (body_inv hi rfl rfl)
  change SegU _ _ _ _ 1011 (facts e L g _ 1010) 1012 (facts e L g _ 1012)
  apply Lib.sum_span false (δ := 213296) (by decide) Flow.code_1011 (by decide)
    (by decide : 505 ∈ ctlLive 1010) _ (fun _ _ => ⟨rfl,rfl⟩) (by decide +kernel)
  exact (Lib.addBase_bits (L.sharedBase+i%2*8) 213296).symm

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

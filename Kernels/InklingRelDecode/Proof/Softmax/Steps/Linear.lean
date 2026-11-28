-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Numeric
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

private theorem advance_body {s z : Site} {op : Op}
    (hc : kernel.code[s.pc]? = some ⟨none,op⟩) (loc : op.isLocal = false)
    (fire : ∀ {t u ev}, Fires s.pc (eventTmpl Assumptions.all L g t op) ev (some u) →
      u = PTX.next t)
    (hn : ∀ ev, next e L g ⟨s,i,v⟩ ev = some (some ⟨z,i,v⟩))
    (live : SiteBody s ∧ SiteBody z)
    (seg : SegU kernel Assumptions.all L g (s.pc+1) (facts e L g ⟨s,i,v⟩ s.pc)
      z.pc (facts e L g ⟨z,i,v⟩ z.pc)) : (code e L g).StepAtU ⟨s,i,v⟩ :=
  step_of_inv fun hi => Code.advanceU (dn := ⟨z,i,v⟩) hc loc fire hn rfl rfl rfl rfl
    (body_inv hi live.1 live.2) seg

theorem step_waitLd : (code e L g).StepAtU ⟨.waitLd,i,v⟩ := by
  apply advance_body (s := .waitLd) (z := .shfl5) Flow.code_tmemWait_1 rfl
    (Code.fires_tcPlain_next (.inr (.inr rfl))) (fun _ => rfl) (by decide)
  exact carry_seg (by decide +kernel) score_to_shuffle

theorem step_waitLdO : (code e L g).StepAtU ⟨.waitLdO,i,v⟩ := by
  apply advance_body (s := .waitLdO) (z := .bar24) Flow.code_tmemWait_2 rfl
    (Code.fires_tcPlain_next (.inr (.inr rfl))) (fun _ => rfl) (by decide)
  exact carry_seg (by decide +kernel) products_to_bar

theorem step_bar22 : (code e L g).StepAtU ⟨.bar22,i,v⟩ := by
  apply advance_body (s := .bar22) (z := .shfl7) Flow.code_bar_22 rfl fires_barSyncN_next
    (fun _ => rfl) (by decide)
  exact project_seg (by decide +kernel)

theorem step_bar23 : (code e L g).StepAtU ⟨.bar23,i,v⟩ := by
  apply advance_body (s := .bar23) (z := .ldL) Flow.code_bar_23 rfl fires_barSyncN_next
    (fun _ => rfl) (by decide)
  exact project_seg (by decide +kernel)

theorem step_entry : (code e L g).StepAtU ⟨.setMaxReg,i,v⟩ := by
  apply step_of_inv
  intro hi
  have hz := hi.init (.inl rfl)
  have dst : Inv e (g % L.block) ⟨.bar0,i,v⟩ :=
    ⟨hi.entry,hi.thread,hi.bound,fun _ => hz,fun _ => nofun,fun _ => nofun,nofun,
      fun _ _ h => (h rfl).elim⟩
  apply Code.advanceU (C := code e L g) (d := ⟨.setMaxReg,i,v⟩) (dn := ⟨.bar0,i,v⟩)
    Flow.code_setMaxReg_1 rfl _ (fun _ => rfl)
    rfl rfl rfl rfl dst
  · exact project_seg (p := 574) (q := 575) (by decide +kernel)
  · intro t u ev fire
    simp only [eventTmpl,SetMaxNReg.tmpl] at fire
    split at fire
    · obtain ⟨_,_,h⟩ := fire
      exact Option.some.inj h
    · cases fire.2

theorem step_handoff : (code e L g).StepAtU ⟨.epilogue,i,v⟩ where
  site := fun _ => ⟨_,Flow.code_mbarWait_5,rfl,trivial⟩
  step := fun _ _ _ _ _ => .inl (.inl rfl)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Close
public import Kernels.InklingRelDecode.Proof.Common.LateThread
import Lemmas.Flow.GlueStep
import Lemmas.Flow.StepForQPGlue
import Kernels.InklingRelDecode.Flow.Code.Part044

@[expose] public section

/-! # The strict window of the epilogue

The states of the window are the epilogue states of the value thread machine without the softmax's
constants (`lateThread`), whose entry the softmax handed over with the zero base word and the
aligned output bases. They step strictly by `step_epi`; the exit has no continuing event. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

noncomputable section

variable {Q : Params} {L : Launch} {g : Nat}

/-- The thread state of the value machine at an epilogue state. -/
abbrev eSt (w : Value) (ent : Softmax.Control.Entry) (z : Epilogue.Control.D) (n : Cls → Nat) :
    (lateThread Q L g).D := (.inr ⟨.inl (.prologue w), .inr ⟨ent, .inr ⟨(), z⟩⟩⟩, n)

/-- What the window needs of the softmax's entry. -/
def EntOkE (ent : Softmax.Control.Entry) : Prop :=
  ent.base = b32 0 ∧ ent.outBase % 4 = 0 ∧ ent.lseBase % 4 = 0

/-- The states of the window. -/
def OkE (d : (lateThread Q L g).D) : Prop :=
  ∃ w ent z n, EntOkE ent ∧ d = eSt w ent z n

/-- The events of the window the epilogue's steps read: the shuffle of the warp index and the
words of the accumulator load. -/
def WfE (ev : Event) : Prop :=
  (ev.pc = 2603 → ∀ m av bv cv recv ok, ev.kind = .shfl m av bv cv recv ok → ∃ x, recv = b32 x) ∧
  (ev.pc = 2607 → ∀ a vals sh, ev.kind = .tc (.ld a vals sh) → ∀ x ∈ vals, Dat32 x)

theorem epiEntry_bases {ent : Softmax.Control.Entry} (ho : ent.outBase % 4 = 0)
    (hl : ent.lseBase % 4 = 0) (t : Nat) :
    (epiEntry ent t).outBase % 4 = 0 ∧ (epiEntry ent t).lseBase % 4 = 0 := by
  unfold epiEntry epiAddr
  split_ifs <;> simp [Epilogue.Control.Entry.outBase, Epilogue.Control.Entry.lseBase, ho, hl]

/-- **The window's states step strictly** on its events. -/
theorem winE_step {R : TState → Prop} (hR : RcpStep L g R)
    (hS : ∀ pc, epiS pc = true → SingleStep kernel Assumptions.all L g R pc)
    (d : (lateThread Q L g).D) (e : Event) (hd : OkE d) :
    (lateThread Q L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) WfE d e := by
  obtain ⟨w, ent, z, n, hok, rfl⟩ := hd
  have h3 : (lateSoftD ent L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) WfE
      (.inr ⟨(), z⟩) e := by
    refine Code.glue_inr_stepForQP (i := ()) ?_
    by_cases hz : z.site = .exit
    · intro ins hat hinv hc hq hw hf hp
      exfalso
      have hpc : (epilogueDCode (epiEntry ent (g % L.block)) L g).pc z = 2855 := by
        change z.site.pc = 2855
        rw [hz]; rfl
      rw [hpc, Flow.code_2855] at hc
      obtain rfl := Option.some.inj hc
      rw [hpc] at hf
      exact absurd hf.2 (by simp)
    · intro ins hat hinv hc hq hw hf hp
      exact step_epi (e := epiEntry ent (g % L.block)) hok.1 hR hS (fun ev h => h.1)
        (fun ev h => h.2) z hz e ins hat hinv hc hq hw hf hp
  have h4 : (lateDataD Q L g w).StepForQP (QTF lateQt)
      (TauAll kernel Assumptions.all L g R) WfE (Sum.inr ⟨ent, Sum.inr ⟨(), z⟩⟩) e :=
    Code.glue_inr_stepForQP (i := ent) h3
  have h5 : (Code.glue (Startup.code Q L g) (Code.withStubs (lateFrag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g))).StepForQP (QTF lateQt)
      (TauAll kernel Assumptions.all L g R) WfE
      (Sum.inr ⟨Sum.inl (Role.prologue w), Sum.inr ⟨ent, Sum.inr ⟨(), z⟩⟩⟩) e :=
    Code.glue_inr_stepForQP (i := Sum.inl (Role.prologue w)) h4
  intro t u ins hat hinv hc hq hw hf hp
  exact Code.counted_stepForQP (cls := cls) (@h5) n ins hat hinv hc hq hw hf hp

end
end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict

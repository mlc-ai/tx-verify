-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.LateThread
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Close
import Lemmas.Flow.GlueStep
import Lemmas.Flow.StepForQPStay
import Lemmas.Flow.StepForQPGlue
import Kernels.InklingRelDecode.Proof.Common.DataSound

@[expose] public section

/-! # The strict window of the softmax and the epilogue behind it

The states of the window are the softmax states of the value thread machine without the constants
(`lateThread`) whose entry has the zero base word and the aligned bases, and the states of the
epilogue behind them. A softmax state steps strictly by `step_soft`; the epilogue states take no
step of the window (its events stay below pc 2565). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

noncomputable section

variable {Q : Params} {L : Launch} {g : Nat}

/-- The thread state of the value machine at a softmax state. -/
abbrev softSt (w : Value) (ent : Control.Entry) (s : Data.D) (n : Cls → Nat) :
    (lateThread Q L g).D := (.inr ⟨.inl (.prologue w), .inr ⟨ent, .inl s⟩⟩, n)

/-- The thread state of the value machine at an epilogue state. -/
abbrev epiSt (w : Value) (ent : Control.Entry) (z : Epilogue.Control.D) (n : Cls → Nat) :
    (lateThread Q L g).D := (.inr ⟨.inl (.prologue w), .inr ⟨ent, .inr ⟨(), z⟩⟩⟩, n)

/-- What the window needs of the entry. -/
def EntOk (ent : Control.Entry) : Prop :=
  ent.base = b32 0 ∧ ent.rel % 2 = 0 ∧ ent.outBase % 4 = 0 ∧ ent.lseBase % 4 = 0

/-- The states of the window. -/
def OkS (d : (lateThread Q L g).D) : Prop :=
  ∃ w ent n, EntOk ent ∧ ((∃ s, d = softSt w ent s n) ∨ ∃ z, d = epiSt w ent z n)

/-- The events of the window: the lane's well-formed ones, below the epilogue. -/
def WfS (e : Event) : Prop := Strict.LWf e ∧ e.pc < 2565

theorem lateSoft_handoff {e : Control.Entry} : Code.Handoff (Data.code e L g)
    (fun _ : Unit => epilogueDCode (epiEntry e (g % L.block)) L g) (fun d => epiExit d.c) := by
  intro d i t hx ht hi
  obtain ⟨pc, sub, acc, flt, regs⟩ := ht
  exact epi_handoff d.c i t hx ⟨pc, sub, acc, flt, ((holds_append _ _ _).mp regs).1⟩ hi

/-- **The window's states step strictly** on its events. -/
theorem winS_step (hsc : Strict.ScaleOk L) (d : (lateThread Q L g).D) (e : Event) (hd : OkS d) :
    (lateThread Q L g).StepForQP (QTF lateQt)
      (TauAll kernel Assumptions.all L g (LateR' L g)) WfS d e := by
  obtain ⟨w, ent, n, hok, ⟨s, rfl⟩ | ⟨z, rfl⟩⟩ := hd
  · have h3 : (lateSoftD ent L g).StepForQP (QTF lateQt)
        (TauAll kernel Assumptions.all L g (LateR' L g)) WfS (.inl s) e := by
      refine Code.glue_inl_stepForQP (fun hx => ?_) lateSoft_handoff
      have hs : s.c.site ≠ .epilogue := by
        intro h
        simp [epiExit, h] at hx
      intro t u ins ha hi hc hq hw hf hp
      exact Strict.step_soft hok.1 hsc s hs e ins ha hi hc hq hw.1 hf hp
    have h4 : (lateDataD Q L g w).StepForQP (QTF lateQt)
        (TauAll kernel Assumptions.all L g (LateR' L g)) WfS (Sum.inr ⟨ent, Sum.inl s⟩) e :=
      Code.glue_inr_stepForQP (i := ent) h3
    have h5 : (Code.glue (Startup.code Q L g) (Code.withStubs (lateFrag Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g))).StepForQP (QTF lateQt)
        (TauAll kernel Assumptions.all L g (LateR' L g)) WfS
        (Sum.inr ⟨Sum.inl (Role.prologue w), Sum.inr ⟨ent, Sum.inl s⟩⟩) e :=
      Code.glue_inr_stepForQP (i := Sum.inl (Role.prologue w)) h4
    intro t u ins hat hinv hc hq hw hf hp
    exact Code.counted_stepForQP (cls := cls) (@h5) n ins hat hinv hc hq hw hf hp
  · have h3 : (lateSoftD ent L g).StepForQP (QTF lateQt)
        (TauAll kernel Assumptions.all L g (LateR' L g)) WfS (.inr ⟨(), z⟩) e := by
      refine Code.glue_inr_stepForQP (i := ()) ?_
      intro t u ins hat hinv hc hq hw hf hp
      have h1 := EventFrame.fires_source_pc hf
      have h2 := (Epilogue.Site.pc_range z.site).1
      have h3 : (epilogueDCode (epiEntry ent (g % L.block)) L g).pc z = z.site.pc := rfl
      have := hw.2
      omega
    have h4 : (lateDataD Q L g w).StepForQP (QTF lateQt)
        (TauAll kernel Assumptions.all L g (LateR' L g)) WfS (Sum.inr ⟨ent, Sum.inr ⟨(), z⟩⟩) e :=
      Code.glue_inr_stepForQP (i := ent) h3
    have h5 : (Code.glue (Startup.code Q L g) (Code.withStubs (lateFrag Q L g) Startup.Entry.pc)
        (Code.gatedExit Startup.enterOf (sel L g))).StepForQP (QTF lateQt)
        (TauAll kernel Assumptions.all L g (LateR' L g)) WfS
        (Sum.inr ⟨Sum.inl (Role.prologue w), Sum.inr ⟨ent, Sum.inr ⟨(), z⟩⟩⟩) e :=
      Code.glue_inr_stepForQP (i := Sum.inl (Role.prologue w)) h4
    intro t u ins hat hinv hc hq hw hf hp
    exact Code.counted_stepForQP (cls := cls) (@h5) n ins hat hinv hc hq hw hf hp

/-- **The window's states are closed under the machine's steps.** -/
theorem winS_next {d d' : (lateThread Q L g).D} {e : Event} (hd : OkS d)
    (hn : (lateThread Q L g).next d e = some (some d')) : OkS d' := by
  obtain ⟨w, ent, n, hok, ⟨s, rfl⟩ | ⟨z, rfl⟩⟩ := hd
  · obtain ⟨hn1, hn2⟩ := Code.counted_next_some hn
    obtain ⟨x', h1, hd1⟩ := Code.glue_inr_some hn1
    obtain ⟨x'', h2, rfl⟩ := Code.glue_inr_some (P := prologueDCode Q L g w)
      (R := fun e => lateSoftD e L g) (exit := fun d => dataExit Q L g w (prologueErase Q L g w d))
      h1
    obtain ⟨d1, h3, rfl⟩ := Code.glue_inl_some h2
    obtain ⟨dd, nn⟩ := d'
    dsimp only at hd1 hn2
    subst hd1
    refine ⟨w, ent, nn, hok, ?_⟩
    by_cases hx : epiExit d1.c = none
    · left
      exact ⟨d1, by rw [Code.enter_none hx]⟩
    · right
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hx
      rw [Code.enter_some hu]
      exact ⟨(epilogueDCode (epiEntry ent (g % L.block)) L g).init, rfl⟩
  · obtain ⟨hn1, hn2⟩ := Code.counted_next_some hn
    obtain ⟨x', h1, hd1⟩ := Code.glue_inr_some hn1
    obtain ⟨x'', h2, rfl⟩ := Code.glue_inr_some (P := prologueDCode Q L g w)
      (R := fun e => lateSoftD e L g) (exit := fun d => dataExit Q L g w (prologueErase Q L g w d))
      h1
    obtain ⟨z1, h3, rfl⟩ := Code.glue_inr_some h2
    obtain ⟨dd, nn⟩ := d'
    dsimp only at hd1 hn2
    subst hd1
    exact ⟨w, ent, nn, hok, Or.inr ⟨z1, rfl⟩⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.ValueSound
public import Lemmas.Kernel.StateMap
public import Lemmas.Flow.TypedG
public import Kernels.InklingRelDecode.Gen.TypedLateQt
import Kernels.InklingRelDecode.Proof.Common.DataSound
import Kernels.InklingRelDecode.Proof.Common.WorkerSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Lemmas.Flow.GlueU
import Lemmas.Flow.GlueUInv
import Lemmas.Flow.CountedU

@[expose] public section

/-! # The value thread machine without the softmax's launch constants

The strict window of a data lane takes its steps from `Softmax.Data.code`; `threadD` holds the
slot with the constants of the value lane (`Softmax.Data.codeS`) added to the facts of every
state. `lateThread` is `threadD` with the slot's facts left at the machine's: the same states and
the same successors, the facts of the states the strict steps prove. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow Softmax

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The softmax's value machine and the epilogue behind it, without the constants. -/
@[reducible] def lateSoftD (e : Control.Entry) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Code.glue (Data.code e L g) (fun _ : Unit => epilogueDCode (epiEntry e (g % L.block)) L g)
    (fun d => epiExit d.c)

/-- The value machine of a data role, without the softmax's constants. -/
@[reducible] def lateDataD (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code kernel Assumptions.all L g :=
  Code.glue (prologueDCode Q L g w) (fun e => lateSoftD e L g)
    (fun d => dataExit Q L g w (prologueErase Q L g w d))

/-- The value fragment of each role of the thread, without the softmax's constants. -/
@[reducible] def lateFrag (Q : Params) (L : Launch) (g : Nat) (r : Role) :
    Code kernel Assumptions.all L g :=
  match r with
  | .dispatch word x => workerCode Q L g word x
  | .prologue word => lateDataD Q L g word

/-- **The value thread machine without the softmax's constants.** -/
@[reducible] def lateThread (Q : Params) (L : Launch) (g : Nat) : Code kernel Assumptions.all L g :=
  Code.roleThread (Startup.code Q L g) (lateFrag Q L g) Startup.Entry.pc Startup.enterOf (sel L g)
    cls

theorem lateSoft_steps {e : Control.Entry} : ∀ d, (lateSoftD e L g).StepAtU d :=
  Code.glue_stepsU (fun d _ => Data.stepAt d) (fun _ d =>
    Code.glue_inr_stepAtU (P := Control.code e L g) (exit := epiExit)
    (soft_steps (e := e) (L := L) (g := g) (.inr ⟨(), d⟩))) (by
    intro d i t hx ht hi
    obtain ⟨pc, sub, acc, flt, regs⟩ := ht
    exact epi_handoff d.c i t hx ⟨pc, sub, acc, flt, ((holds_append _ _ _).mp regs).1⟩ hi)

theorem lateData_steps {w : Value} (hp : Pre Q L m) (hg : g < L.threads) :
    ∀ d, (lateDataD Q L g w).StepAtU d :=
  Code.glue_stepsU (fun d _ => Prologue.Data.step_at hp d) (fun _ d => lateSoft_steps d) (by
    intro d e t hx ht hi
    obtain ⟨pc, sub, acc, flt, regs⟩ := ht
    obtain ⟨a, b⟩ := data_handoff hp hg (prologueErase Q L g w d) e t hx
      ⟨pc, sub, acc, flt, ((holds_append _ _ _).mp regs).1⟩ hi
    have h525 : t.regs 525 = some (Data.scaleVal L) :=
      holds_mem ((holds_append _ _ _).mp regs).2 (Prologue.Data.scale_mem (Q := Q) (g := g) d)
    obtain ⟨a1, a2, a3, a4, a5⟩ := a
    exact ⟨⟨a1, a2, a3, a4, (holds_append _ _ _).mpr ⟨a5, h525, trivial⟩⟩, b, rfl⟩)

theorem lateThread_handoff : Code.Handoff (Startup.code Q L g)
    (Code.withStubs (lateFrag Q L g) Startup.Entry.pc)
    (Code.gatedExit Startup.enterOf (sel L g)) := by
  refine Code.handoff_gated (fun d r h _ => stub_at d r h) ?_
  intro d r i t hr hs hat hinv
  obtain ⟨hA, hI⟩ := thread_handoff d r i t hr hs hat hinv
  cases i with
  | dispatch => exact ⟨hA, hI⟩
  | prologue w =>
    have h27 : d.site.pc = 27 := by
      cases r <;> first | exact (stub_at (Q := Q) (L := L) (g := g) d _ hr).1 | cases hs
    obtain ⟨a1, a2, a3, a4, a5⟩ := hA
    exact ⟨⟨a1, a2, a3, a4, (holds_append _ _ _).mpr ⟨a5, start_facts h27 hat⟩⟩, hI⟩

/-- **The value thread machine without the constants is sound.** -/
theorem lateThread_sound (hp : Pre Q L m) (hg : g < L.threads) : (lateThread Q L g).SoundU := by
  refine Code.counted_soundU (Code.glue_soundU (start hp) (fun d hx =>
    (startup_steps hp d (Code.gatedExit_none.mp hx)).toStepAtU) ?_ lateThread_handoff)
  rintro (i | r) d
  · cases i with
    | dispatch => exact worker_steps hp d
    | prologue => exact lateData_steps hp hg d
  · exact (Code.stop_steps (by cases r <;> decide +kernel) d).toStepAtU

/-- The erasure of a state of the softmax and epilogue to the control machine's. -/
def lateSoftErase (e : Control.Entry) (L : Launch) (g : Nat) :
    (lateSoftD e L g).D → (softCode e L g).D :=
  Code.eraseSumH (fun d : Data.D => d.c) (fun _ => id)

/-- The erasure of a value state of a data role. -/
def lateDataErase (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    (lateDataD Q L g w).D → (dataCode Q L g w).D :=
  Code.eraseSumH (prologueErase Q L g w) (fun e => lateSoftErase e L g)

/-- The erasure of a state of the value fragment of a role. -/
def lateFragErase (Q : Params) (L : Launch) (g : Nat) :
    ∀ r, (lateFrag Q L g r).D → (frag Q L g r).D
  | .dispatch _ _ => id
  | .prologue word => lateDataErase Q L g word

/-- The erasure of a state of `lateThread` to the control thread's. -/
def lateErase (Q : Params) (L : Launch) (g : Nat) (s : (lateThread Q L g).D) : (thread Q L g).D :=
  (Code.eraseSum (Code.eraseStubs (lateFragErase Q L g)) s.1, s.2)

theorem lateFrag_erases (Q : Params) (L : Launch) (g : Nat) :
    ∀ r, Code.Erases (lateFrag Q L g r) (frag Q L g r) (lateFragErase Q L g r)
  | .dispatch _ _ => Code.Erases.rfl' _
  | .prologue w => Code.Erases.glueHead (prologue_erases Q L g w) (fun _ => rfl)
      fun e => Code.Erases.glueHead ((Data.over e L g).erases rfl) (fun _ => rfl)
        fun _ => Code.Erases.rfl' _

theorem lateThread_erases : Code.Erases (lateThread Q L g) (thread Q L g) (lateErase Q L g) :=
  Code.Erases.roleThread (lateFrag_erases Q L g)

theorem lateThread_stepMap : Frame.StepMap (lateThread Q L) (thread Q L) (lateErase Q L) where
  init g := lateThread_erases.init
  next g s e := by
    obtain ⟨a, n⟩ := s
    symm
    rcases a with b | ⟨j | r, x⟩
    · simp only [thread, lateThread, lateErase, Code.roleThread, Code.counted, Code.glue,
        Code.eraseSum]
      rcases Startup.succ L g b e with _ | _ | c
      · rfl
      · rfl
      · simp only [Option.map_some]
        unfold Code.enter
        cases hx : Code.gatedExit (P := Startup.code Q L g) Startup.enterOf (sel L g) c with
        | none => rfl
        | some j =>
          rcases j with i | r
          · simp only [lateErase, Code.eraseSum, Code.eraseStubs]
            rw [(lateFrag_erases Q L g i).init]
          · rfl
    · cases j with
      | dispatch w x' =>
        simp only [thread, lateThread, lateErase, Code.roleThread, Code.counted, Code.glue,
          Code.withStubs, frag, lateFrag, lateFragErase, Code.eraseSum, Code.eraseStubs]
        rcases (workerCode Q L g w x').next x e with _ | _ | c <;> simp <;> rfl
      | prologue w =>
        simp only [thread, lateThread, lateErase, Code.roleThread, Code.counted, Code.glue,
          Code.withStubs, frag, lateFrag, lateFragErase, Code.eraseSum, Code.eraseStubs]
        simp only [lateDataErase, Code.eraseSumH, dataCode, lateDataD]
        rcases x with d | ⟨en, y⟩
        · rcases hn : Prologue.Control.next Q L g d.c e with _ | _ | c
          · simp [Prologue.Data.succ, prologueErase, hn]
          · simp [Prologue.Data.succ, prologueErase, hn]; rfl
          · simp only [Prologue.Data.succ, prologueErase, hn, Option.map_some]
            unfold Code.enter
            cases hx : dataExit Q L g w c <;> simp only [hx] <;> rfl
        · rcases y with y | ⟨u, y⟩
          · rcases hn : Control.next en L g y.c e with _ | _ | c
            · simp [Data.succ, lateSoftErase, Code.eraseSumH, hn]
            · simp [Data.succ, lateSoftErase, Code.eraseSumH, hn]
            · simp only [Data.succ, lateSoftErase, Code.eraseSumH, hn, Option.map_some]
              unfold Code.enter
              cases hx : epiExit c <;> simp only [hx] <;> rfl
          · rcases hn : Epilogue.Control.next (epiEntry en (g % L.block)) L g y e with _ | _ | c <;>
              simp [lateSoftErase, Code.eraseSumH, hn]
            rfl
    · rfl

/-- **The value thread machine without the constants follows the lane.** -/
theorem lateFollowed {X : Execution} (hf : Follow Q L X) (hg : g < L.threads) (k : Nat) :
    Frame.FollowedAt (lateThread Q L) (fun g σ => guardedTable Q L g (lateErase Q L g σ)) X g
      k := by
  have hm := Frame.stateAt_map (lateThread_stepMap (Q := Q) (L := L)) X g k
  refine ⟨fun h => ?_, fun d hd => ?_⟩
  · rw [h] at hm
    exact (hf g hg k).1 hm.symm
  · exact (hf g hg k).2 _ (Frame.stateAt_map_some lateThread_stepMap hd)


/-- **The lane is at the first state of the epilogue before its event `i`**: the value thread
machine's state there, the entry's facts the epilogue's window needs, and the stop state at which
the event fires, with the machine's facts and the tags of the lane. -/
structure EpiAt (Q : Params) (L : Launch) (X : Execution) (g i : Nat) : Prop where
  state : ∃ w ent z n, Frame.stateAt (lateThread Q L) X g i =
    some (some (.inr ⟨.inl (.prologue w), .inr ⟨ent, .inr ⟨(), z⟩⟩⟩, n)) ∧
    ent.base = b32 0 ∧ ent.outBase % 4 = 0 ∧ ent.lseBase % 4 = 0
  stop : ∀ d ei, Frame.stateAt (lateThread Q L) X g i = some (some d) → X.get (g, i) = some ei →
    ∃ t0 t1 o', Run kernel Assumptions.all L g {} ((X.tr g).take i) (some t0) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 ∧
      (lateThread Q L g).Good (some d) t1 ∧ EStep kernel Assumptions.all L g t1 ei o'
  typed : ∀ d t0 t1, Frame.stateAt (lateThread Q L) X g i = some (some d) →
    Run kernel Assumptions.all L g {} ((X.tr g).take i) (some t0) →
    Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t1 →
    (lateThread Q L g).Good (some d) t1 → PTX.Flow.TyG.QTF Gen.TypedLateQt.lateQt t1

end
end PTX.Kernels.InklingRelDecode.Proof

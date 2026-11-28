-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Sound
public import Kernels.InklingRelDecode.Proof.Common.ValueThread
public import Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Table
import Lemmas.Flow.GlueU
import Lemmas.Flow.CountedU
import Kernels.InklingRelDecode.Proof.Common.DataSound
import Kernels.InklingRelDecode.Proof.Common.WorkerSound

@[expose] public section

/-! # The value thread machine is sound and followed

`threadD_sound`: `threadD` follows every launched thread as `thread` does. Until a value slot
replaces its control machine this is `thread_sound`; a value lane then adds its slot's steps
(`Over.stepAtU`) and first state here. `followD`: along a followed trace a value state erases to
a control state that satisfies the table, so a value export needs no premise beyond `Follow`. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The steps of the value machine of a data role. -/
theorem dataD_steps {w : Value} (hp : Pre Q L m) (hg : g < L.threads) :
    ∀ d, (dataDCode Q L g w).StepAtU d :=
  Code.glue_stepsU (fun d _ => Prologue.Data.step_at hp d) (fun _ d => softD_steps d) (by
    intro d e t hx ht hi
    obtain ⟨pc, sub, acc, flt, regs⟩ := ht
    obtain ⟨a, b⟩ := data_handoff hp hg (prologueErase Q L g w d) e t hx
      ⟨pc, sub, acc, flt, ((holds_append _ _ _).mp regs).1⟩ hi
    have h525 : t.regs 525 = some (Softmax.Data.scaleVal L) :=
      holds_mem ((holds_append _ _ _).mp regs).2 (Prologue.Data.scale_mem (Q := Q) (g := g) d)
    obtain ⟨a1, a2, a3, a4, a5⟩ := a
    have hS := data_start (w := w) hx ⟨pc, sub, acc, flt, ((holds_append _ _ _).mp regs).1⟩
    have hC := (Softmax.Data.constF_init e L g).symm ▸ hS
    exact ⟨⟨a1, a2, a3, a4, (holds_append _ _ _).mpr
      ⟨(holds_append _ _ _).mpr ⟨a5, h525, trivial⟩, hC⟩⟩, b, rfl⟩)

/-- The scale and stride facts the startup leaves at the prologue's first site. -/
theorem start_facts {d : Startup.D} {t : TState}
    (hpc : d.site.pc = 27) (hat : (Startup.code Q L g).AtD d t) :
    Holds t.regs (Prologue.Data.dF Q L g {}) := by
  obtain ⟨-, -, -, -, hregs'⟩ := hat
  have hregs : Holds t.regs (factsFrom (Flow.live d.site.pc) (Startup.valueOf Q L g d)) := hregs'
  rw [hpc] at hregs
  have hv := fun r (hr : r ∈ Flow.live 27) => holds_mem hregs (mem_factsFrom hr)
  have h525 := hv 525 (by rw [Startup.live27]; decide)
  have h529 := hv 529 (by rw [Startup.live27]; decide)
  have h530 := hv 530 (by rw [Startup.live27]; decide)
  have h531 := hv 531 (by rw [Startup.live27]; decide)
  exact ⟨h525, h529, h530, h531, trivial⟩

theorem threadD_handoff : Code.Handoff (Startup.code Q L g)
    (Code.withStubs (fragD Q L g) Startup.Entry.pc) (Code.gatedExit Startup.enterOf (sel L g)) := by
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

theorem threadD_sound (hp : Pre Q L m) (hg : g < L.threads) : (threadD Q L g).SoundU := by
  refine Code.counted_soundU (Code.glue_soundU (start hp) (fun d hx =>
    (startup_steps hp d (Code.gatedExit_none.mp hx)).toStepAtU) ?_ threadD_handoff)
  · rintro (i | r) d
    · cases i with
      | dispatch => exact worker_steps hp d
      | prologue => exact dataD_steps hp hg d
    · exact (Code.stop_steps (by cases r <;> decide +kernel) d).toStepAtU

/-- **A followed value state erases to a control state that satisfies the table.** -/
theorem followD {X : Execution} (hF : Follow Q L X) (hg : g < L.threads) {k : Nat}
    {s : (threadD Q L g).D} (hs : Frame.stateAt (threadD Q L) X g k = some (some s)) :
    guardedTable Q L g (eraseThread Q L g s) :=
  (hF g hg k).2 _ (control_of_data hs)

end PTX.Kernels.InklingRelDecode.Proof

-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.StartupCode
public import Kernels.FlashKdaFwd.Packed.RegisterFrame

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof PTX.EventFrame

private def advances (t u : TState) : Prop :=
  u.pc = t.pc+1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault

private theorem shuffle {L : Launch} {g : Nat} {t : TState} {m : ShflMode} {d : Nat}
    {p : Option Nat} {a b c mask : Opnd} :
    CallbackFrame (advances t) (shflTmpl L g t m d p a b c mask) := by
  cases p <;> unfold shflTmpl
  all_goals repeat' split
  all_goals simp [CallbackFrame,advances,next,setReg]

private theorem elect {L : Launch} {g : Nat} {t : TState} {d : Option Nat} {p : Nat}
    {mask : Opnd} : CallbackFrame (advances t) (electTmpl L g t d p mask) := by
  cases d <;> unfold electTmpl
  all_goals repeat' split
  all_goals simp [CallbackFrame,advances,next,setReg]

private theorem warp {L : Launch} {g : Nat} {t : TState} {w : WarpInstr}
    (kind : startupEvent (.warp w) = true) :
    CallbackFrame (advances t) (warpTmpl L g t w) := by
  unfold warpTmpl
  split
  all_goals first | exact shuffle | exact elect | trivial | simp_all [startupEvent]

private theorem barrier {L : Launch} {g : Nat} {t : TState} {a : Opnd} :
    CallbackFrame (advances t) (barTmpl L g t a none .sync) := by
  unfold barTmpl
  repeat' split
  all_goals simp [CallbackFrame,advances,next]

private theorem initial {L : Launch} {g : Nat} {t : TState} {r : Nat} {off : Int} {n : Opnd} :
    CallbackFrame (advances t) (tmaTmpl L g t (.mbarInit r off n)) := by
  unfold tmaTmpl
  apply ofExec_frame
  repeat' first | apply allOk_bind; intro _ | split | exact trivial | exact ⟨rfl,rfl,rfl,rfl⟩

theorem startup_event_frame {base : Nat → Nat → Nat} {L : Launch} {g : Nat} {t u : TState}
    {i : Instr} {e : Event} (kind : startupEvent i.op = true)
    (fire : Fires t.pc (eventTmpl (Prologue.assumptions base) L g t i.op) e (some u)) :
    u.pc = t.pc+1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault := by
  apply callbackFrame_fires (P := advances t) _ fire
  cases op : i.op <;> simp only [op,startupEvent] at kind <;> try contradiction
  · exact warp kind
  · exact barrier
  · change CallbackFrame (advances t) (tmaTmpl L g t (.mbarInit ..))
    exact initial
  · exact ⟨rfl,rfl,rfl,rfl⟩

end FlashKda.Packed.ProducerControl

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
public import Lemmas.Kernel.GlueStrict
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Every startup event is its site's event

The thread machine follows a thread through a final undefined behaviour at any state
(`thread_sound`), so its trace alone does not place an event at a startup state on the startup's
site. The strict glue (`Lemmas/Kernel/GlueStrict.lean`: the roles stop at their first event) is
sound from the startup's strict steps, the fragments' site obligations and the hand-off
(`strict_sound`), and its states agree with the thread machine's on the startup's states, so an
event at a startup state is the event of the startup's site: it has the startup's shape and its pc
is its site's (`startup_ev`), undefined behaviour included. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The thread machine whose warpgroups and stubs stop at their first event. -/
abbrev strictC (P : Params) (L : Launch) (g : Nat) : Code kernel Assumptions.all L g :=
  Code.strictThread (startupCode P L g) (frag P L g) Entry.pc (startupEnter P L g) (sel P L g) cls

/-- **The strict thread machine is sound.** -/
theorem strict_sound (hp : Pre P L m) : (strictC P L g).Sound :=
  Code.strictThread_sound (startup_start hp) (startup_steps hp) (frag_stepsU hp) thread_handoff

/-- A startup state that is not an exit sits at pc 97 or below. -/
theorem startup_pc_le {d : Startup.D} (hx : startupEnter P L g d = none) : d.site.pc ≤ 97 := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => fin_cases j <;> simp [Startup.Site.pc]
  | elect j => fin_cases j <;> simp [Startup.Site.pc]
  | init n => fin_cases n <;> simp [Startup.Site.pc, Startup.initPc]
  | enter r => simp [startupEnter, Startup.exitOf] at hx
  | _ => simp [Startup.Site.pc]

/-- **An event at a startup state is its site's event**: it has the startup's shape at the site's
pc, and the state is no exit. -/
theorem startup_ev (hp : Pre P L m) {X : Execution} (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {d : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inl d, n))) :
    Startup.Ev L g d e ∧ e.pc = d.site.pc ∧ startupEnter P L g d = none := by
  have hσ' : Frame.stateAt (strictC P L) X g k = some (some (.inl d, n)) := Code.strict_recover hσ
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (C := strictC P L) (fun _ _ => strict_sound hp) hX he hσ'
  exact ⟨Startup.shape hp hat hi.1 hc hf, EventFrame.fires_source_pc hf,
    Code.gatedExit_none.mp hi.2⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

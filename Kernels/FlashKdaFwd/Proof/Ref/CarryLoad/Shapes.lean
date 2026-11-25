-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Steps

@[expose] public section

/-! # The events of the CarryLoad phase, in closed form

`Ev P g pos e`: what the event `e` fired at a state of position `pos` is.

* `ld j` (the generic `ld.b32 %r, [%rd]` at instruction `765 + 5 j`): a read of the four bytes
  at `ldAddr P g j`, the swizzled address of the thread's base pointer plus the constant of the
  load, in the shared window of the thread's own block. The address is a multiple of four
  inside the FP32 state buffer (`Lib.lean: ldAddr_frame`);
* `fence` (`fence.proxy.async.shared::cta` at instruction 1401): the proxy fence.

`barEv` is the event of the exit state (`bar.sync 0` at instruction 1402).

`ev_at`: the event fired at a state of the invariant is the position's; `ev_exit`: the event
fired at the exit state is `barEv`. All three kinds are exact: none of these events is
undefined behaviour (`Ev.noUb`), whatever the data. The bytes a load returns are not
constrained here; that they have a value is the data condition of `Trace.lean`.

`Ev.led`, `Ev.kind_cases`: an event of the phase is in no class of the startup's ledger, and
it is a read of shared memory or a proxy fence (for the count transport of `Links.lean`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- **The event of a position**, in closed form. -/
def Ev (P : Params) (g : Nat) : Pos → Event → Prop
  | .ld j, e => ∃ bs, bs.length = 4 ∧ e = ⟨765 + 5 * j.val,
      .rd { loc := ⟨.shared, cta g, ldAddr P g j.val⟩, size := 4 } bs⟩
  | .fence, e => e = ⟨1401, .fenceProxy (.async (some (.shared .cta))) none⟩

/-- **The event of the exit state**: the `bar.sync 0` of instruction 1402. -/
def barEv : Event := ⟨1402, .bar 0 none .sync⟩

/-- **The event of a state of the invariant is the position's.** -/
theorem ev_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩) (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t)
    (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) : Ev P g pos e := by
  cases pos with
  | ld j =>
    obtain ⟨hcm, -, hp⟩ := h.pos
    obtain ⟨-, -, f3, f4, -⟩ := ldAddr_frame hpre hcm j.isLt
    obtain ⟨bs, hbs, rfl⟩ := ev_ld hpre hg j.isLt hat hc hf hp f4 f3
    exact ⟨bs, hbs, by rw [ldSite_pc j.val j.isLt]⟩
  | fence =>
    have hc' : kernel.code[1401]? = some ins := hc
    obtain rfl := Option.some.inj (hc'.symm.trans (by code_lookup))
    exact ev_fence hf

/-- **The event of the exit state** is the `bar.sync 0` of instruction 1402. -/
theorem ev_exit (hc : kernel.code[1402]? = some ins)
    (hf : Fires 1402 (eventTmpl Assumptions.all L g t ins.op) e o) : e = barEv := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  exact ev_bar0 hf

/-- An event of the phase is not undefined behaviour. -/
theorem Ev.noUb {pos : Pos} (h : Ev P g pos e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  cases pos with
  | ld j =>
    obtain ⟨bs, -, rfl⟩ := h
    intro _ _ h'
    cases h'
  | fence =>
    obtain rfl := h
    intro _ _ h'
    cases h'

/-- An event of the phase is in no class of the startup's ledger. -/
theorem Ev.led {pos : Pos} (h : Ev P g pos e) : Startup.ledEv e = ⟨0, 0, 0, 0, 0, 0⟩ := by
  cases pos with
  | ld j =>
    obtain ⟨bs, -, rfl⟩ := h
    rfl
  | fence =>
    obtain rfl := h
    rfl

/-- **An event of the phase is a read of shared memory or a proxy fence.** -/
theorem Ev.kind_cases {pos : Pos} (h : Ev P g pos e) :
    (∃ a bs, e.kind = .rd a bs ∧ a.loc.space = .shared) ∨ ∃ px sc, e.kind = .fenceProxy px sc := by
  cases pos with
  | ld j =>
    obtain ⟨bs, -, rfl⟩ := h
    exact .inl ⟨_, bs, rfl, rfl⟩
  | fence =>
    obtain rfl := h
    exact .inr ⟨_, _, rfl⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad

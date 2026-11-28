-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Safe
import Lemmas.Flow.NotObject
import Lemmas.Flow.ShflKind
import Lemmas.Flow.LoadAt
import Lemmas.Flow.Step.ShapeRegs
import Lemmas.Flow.MemTmpl
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part034
import Kernels.InklingRelDecode.Flow.Code.Part035

@[expose] public section

/-! # The softmax is not lost on an event that is not undefined behaviour

The successor of a state of the softmax but the hand-off is `none` only on a poll site fired by
something that is no poll, on a shuffle site fired by something that is no shuffle, or on the
shared load of the row sum fired by something that is no read. The template of each fires its own
kind of event or undefined behaviour. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g : Nat} {t : TState} {ins : Instr}

/-- A shuffle site fires a shuffle or undefined behaviour. -/
theorem fires_shfl_site {pc : Nat} (hc : kernel.code[pc]? = some ins) (h : shflShape pc = true)
    {v : Event} {o : Option TState} (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) v o) :
    (∃ m av bv cv recv ok, v.kind = .shfl m av bv cv recv ok) ∨ ∃ f, v.kind = .ub f := by
  unfold shflShape at h
  rw [hc] at h
  obtain ⟨gd, op⟩ := ins
  split at h
  · rename_i m d r b c hm
    simp only [Option.some.injEq, Instr.mk.injEq] at hm
    obtain ⟨-, rfl⟩ := hm
    simp only [eventTmpl, warpTmpl] at hf
    rcases fires_shflTmpl_kind hf with ⟨av, bv, cv, recv, ok, hk⟩ | ⟨f, hk⟩
    · exact .inl ⟨_, av, bv, cv, recv, ok, hk⟩
    · exact .inr ⟨f, hk⟩
  · cases h

/-- **The successor of a state of the softmax but the hand-off on an event that is not undefined
behaviour is not `none`.** -/
theorem live_soft {d : Data.D} {v : Event} {o : Option TState} (hs : d.c.site ≠ .epilogue)
    (hc : kernel.code[d.c.site.pc]? = some ins)
    (hf : Fires d.c.site.pc (eventTmpl Assumptions.all L g t ins.op) v o)
    (hu : ∀ f, v.kind ≠ .ub f) : Data.succ e L g d v ≠ none := by
  have key : Control.next e L g d.c v ≠ none → Data.succ e L g d v ≠ none := by
    intro h hn
    exact h (Option.map_eq_none_iff.mp hn)
  apply key
  have shfl : shflShape d.c.site.pc = true →
      ∃ m av bv cv recv ok, v.kind = .shfl m av bv cv recv ok :=
    fun h => (fires_shfl_site hc h hf).elim id fun ⟨f, hk⟩ => absurd hk (hu f)
  obtain ⟨c, vs⟩ := d
  obtain ⟨s, i, hd⟩ := c
  cases hsite : s <;> simp only [hsite] at hs hc hf shfl <;> try simp [Control.next]
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1257)
    rcases fires_mbarWait_kind hf with ⟨m, q, ok, acq, sc, hk⟩ | ⟨f, hk⟩
    · cases ok <;> simp [hk]
    · exact absurd hk (hu f)
  · obtain ⟨m, av, bv, cv, recv, ok, hk⟩ := shfl (by decide +kernel)
    simp [hk]
  · obtain ⟨m, av, bv, cv, recv, ok, hk⟩ := shfl (by decide +kernel)
    simp [hk]
  · obtain ⟨m, av, bv, cv, recv, ok, hk⟩ := shfl (by decide +kernel)
    simp [hk]
  · obtain ⟨m, av, bv, cv, recv, ok, hk⟩ := shfl (by decide +kernel)
    simp [hk]
  · obtain ⟨m, av, bv, cv, recv, ok, hk⟩ := shfl (by decide +kernel)
    simp [hk]
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2252)
    rw [eventTmpl, memTmpl_load rfl rfl rfl rfl rfl] at hf
    rcases fires_load_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · simp [hk]
    · exact absurd hk (hu f)
  · obtain ⟨m, av, bv, cv, recv, ok, hk⟩ := shfl (by decide +kernel)
    simp [hk]
  · obtain ⟨m, av, bv, cv, recv, ok, hk⟩ := shfl (by decide +kernel)
    simp [hk]
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2239)
    rcases fires_mbarWait_kind hf with ⟨m, q, ok, acq, sc, hk⟩ | ⟨f, hk⟩
    · cases ok <;> simp [hk]
    · exact absurd hk (hu f)
  · split <;> simp

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict

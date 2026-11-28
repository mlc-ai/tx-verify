-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.WaitLd
public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Shfl
public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Load
public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Tail

@[expose] public section

/-! # The strict step of every site of the epilogue

`step_epi` dispatches on the site; the exit has none (a glued machine leaves the epilogue at the
exit, so it never holds a state there). The hypotheses are the facts of the assembly: the base word
of the entry (`Iface.BaseRead`), the single pieces of the data lane's invariant, the reciprocal at
2602, the received word of the shuffle and the words of the accumulator load. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

variable {e : Entry} {L : Launch} {g : Nat} {R : TState → Prop} {Wf : Event → Prop}

/-- **Every state of the epilogue but the exit steps strictly.** -/
theorem step_epi (hb : e.base = b32 0) (hR : RcpStep L g R)
    (hS : ∀ pc, epiS pc = true → SingleStep kernel Assumptions.all L g R pc)
    (hW : ∀ ev, Wf ev → ev.pc = 2603 → ∀ m av bv cv recv ok,
      ev.kind = .shfl m av bv cv recv ok → ∃ x, recv = b32 x)
    (hD : ∀ ev, Wf ev → ev.pc = 2607 → ∀ a vals sh, ev.kind = .tc (.ld a vals sh) →
      ∀ x ∈ vals, Dat32 x) (d : D) (hs : d.site ≠ .exit) (ev : Event) :
    (code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) Wf d ev := by
  obtain ⟨s, v⟩ := d
  cases s with
  | wait => exact sstep_wait hR ev
  | shfl => exact sstep_shfl hb hW ev
  | load => exact sstep_load hD ev
  | waitLd => exact sstep_waitLd hS ev
  | lse => exact sstep_lse ev
  | store j => exact sstep_store j ev
  | join => exact sstep_join ev
  | setMax => exact sstep_setMax ev
  | roleWord => exact sstep_roleWord ev
  | sync1 => exact sstep_sync1 ev
  | sync0 => exact sstep_sync0 ev
  | dealloc => exact sstep_dealloc ev
  | exit => exact absurd rfl hs

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict

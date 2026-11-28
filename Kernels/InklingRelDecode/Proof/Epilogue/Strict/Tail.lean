-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Base
import Kernels.InklingRelDecode.Flow.Code.Part044
import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
import Lemmas.Flow.SegJump
import Lemmas.Flow.Async
import Lemmas.Flow.IssueNext

@[expose] public section

/-! # The strict steps of the closing sites: the barriers, the role word and the deallocation -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {R : TState → Prop} {Wf : Event → Prop} {v : Value}

theorem sstep_join (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.join, v⟩ ev :=
  adv_site (s' := .setMax) (p := 2846) rfl rfl Flow.code_2846 (fires_async_next trivial)
    (fun _ => rfl) (fun _ => trivial) (by decide +kernel) (by decide +kernel) ev

theorem sstep_setMax (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.setMax, v⟩ ev :=
  adv_site (s' := .roleWord) (p := 2847) rfl rfl Flow.code_2847
    (fun hf => by obtain ⟨_, _, h⟩ := hf; exact Option.some.inj h) (fun _ => rfl)
    (fun _ => trivial) (by decide +kernel)
    (by decide +kernel) ev

theorem sstep_sync1 (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.sync1, v⟩ ev :=
  adv_site (s' := .sync0) (p := 2849) rfl rfl Flow.code_2849 (fires_async_next trivial)
    (fun _ => rfl) (fun _ => trivial) (by decide +kernel) (by decide +kernel) ev

/-- The jump over the second deallocation to the return. -/
theorem jump_exit {v : Value} {q : Nat} (hq : ∀ r ∈ ctlLive 2855, r ∈ ctlLive q) :
    SegQ kernel Assumptions.all L g (QTF lateQt) 2852 (facts e L g v q) 2855
      (facts e L g v 2855) :=
  (SegQF.jmp Flow.code_2852 (fun t _ => Lib.bra_rule t) (segFree (by decide))
    (by decide +kernel)).comp (SegQ.weaken fun _ hR => holds_of_forall fun a ha =>
      holds_mem hR (fsub (v := v) hq a ha))

theorem sstep_dealloc (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.dealloc, v⟩ ev :=
  adv_gen (s' := .exit) (p := 2851) rfl Flow.code_2851 (fires_async_next trivial)
    (fun _ => rfl) (fun _ => trivial) (by decide +kernel)
    (SegQ.tauAll R (jump_exit (by decide +kernel))) ev

theorem sstep_roleWord (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.roleWord, v⟩ ev :=
  Code.StepForQ.toP _ (Code.scalarStoreF (C := code e L g) (d := ⟨.roleWord, v⟩)
    (dn := ⟨.sync1, v⟩) Flow.code_2848 rfl rfl (fun _ => rfl) rfl rfl rfl rfl trivial
    (by change afterF lateQt 2848 [] = true; decide +kernel)
    (seg_step (s' := .sync1) (v := v) (p := 2848) rfl (by decide +kernel)) ev)

theorem sstep_sync0 (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.sync0, v⟩ ev := by
  by_cases h : g % L.block < 32
  · exact adv_site (s' := .dealloc) (p := 2850) rfl rfl Flow.code_2850
      (fires_async_next trivial) (fun _ => by simp [Control.next, h]) (fun _ => h)
      (by decide +kernel) (by decide +kernel) ev
  · have off : valueOf e L g v 3 = .pred false := congrArg Value.pred (decide_eq_false h)
    refine adv_gen (s' := .exit) (p := 2850) rfl Flow.code_2850 (fires_async_next trivial)
      (fun _ => by simp [Control.next, h]) (fun _ => trivial) (by decide +kernel)
      (SegQ.tauAll R ((SegQF.skipG Flow.code_2851 (pick := false) (F := facts e L g v 2850)
        (G := facts e L g v 2850)
        (fun _ hR => holds_mem hR (mem_factsFrom_eq (by decide : 3 ∈ ctlLive 2850) off))
        rfl (fun _ h => h) (by decide +kernel)).comp (jump_exit (by decide +kernel)))) ev

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict

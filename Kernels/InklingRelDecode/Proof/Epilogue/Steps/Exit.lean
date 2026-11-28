-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Base
import Kernels.InklingRelDecode.Flow.Code.Part044
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.SegJump
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof
set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Value}

theorem step_join : (code e L g).StepAtU ⟨.join,v⟩ := by
  apply straight (s := .join) (z := .setMax) Flow.code_2846 rfl (fun _ => trivial)
    (fun _ => fires_async_next trivial) (fun _ => rfl) (fun _ => trivial)
    (Lib.control_span (by decide +kernel))

theorem step_setMax : (code e L g).StepAtU ⟨.setMax,v⟩ := by
  apply straight (s := .setMax) (z := .roleWord) Flow.code_2847 rfl (fun _ => trivial) _
    (fun _ => rfl) (fun _ => trivial) (Lib.control_span (by decide +kernel))
  intro t ev u _ hf
  obtain ⟨_,_,h⟩ := hf
  exact Option.some.inj h

theorem step_roleWord : (code e L g).StepAtU ⟨.roleWord,v⟩ := by
  apply Code.vstU (C := code e L g) (d := ⟨.roleWord,v⟩) (dn := ⟨.sync1,v⟩)
    Flow.code_2848 rfl rfl (fun _ => rfl) rfl
  · exact fun h => (Nat.lt_irrefl 1 h).elim
  · intro _
    exact ⟨rfl,rfl,trivial,Lib.control_span (by decide +kernel :
      Lib.spanCheck ctlLive 2848 2849 2849)⟩

theorem step_sync1 : (code e L g).StepAtU ⟨.sync1,v⟩ := by
  apply straight (s := .sync1) (z := .sync0) Flow.code_2849 rfl (fun _ => trivial)
    (fun _ => fires_async_next trivial) (fun _ => rfl) (fun _ => trivial)
    (Lib.control_span (by decide +kernel))

private theorem tail_jump {p : Nat} (h : Lib.spanCheck ctlLive p 2855 2855) :
    SegU kernel Assumptions.all L g 2852 (facts e L g v p) 2855 (facts e L g v 2855) :=
  (SegU.of_seg (seg_jmp Flow.code_2852 (fun t _ => Lib.bra_rule t) (segFree (by decide)))).comp
    (Lib.control_span h)

theorem step_dealloc : (code e L g).StepAtU ⟨.dealloc,v⟩ := by
  apply straight (s := .dealloc) (z := .exit) Flow.code_2851 rfl _
    (fun _ => fires_async_next trivial)
    (fun _ => rfl) (fun _ => trivial) (tail_jump (by decide +kernel))
  intro hi
  apply Code.guardTrue_factsFrom (by decide : 3 ∈ ctlLive 2851)
  exact congrArg Value.pred (decide_eq_true hi)

theorem step_sync0 : (code e L g).StepAtU ⟨.sync0,v⟩ := by
  by_cases h : g%L.block < 32
  · apply straight (s := .sync0) (z := .dealloc) Flow.code_2850 rfl (fun _ => trivial)
      (fun _ => fires_async_next trivial) (fun _ => by simp [next,h]) (fun _ => h)
      (Lib.control_span (by decide +kernel))
  · apply straight (s := .sync0) (z := .exit) Flow.code_2850 rfl (fun _ => trivial)
      (fun _ => fires_async_next trivial) (fun _ => by simp [next,h]) (fun _ => trivial)
    have off : valueOf e L g v 3 = .pred false := congrArg Value.pred (decide_eq_false h)
    exact (SegU.of_seg (Seg.guardSkip Flow.code_2851
      (mem_factsFrom_eq (by decide : 3 ∈ ctlLive 2850) off) rfl)).comp
      (tail_jump (by decide +kernel))

theorem step_exit : (code e L g).StepAtU ⟨.exit,v⟩ := by
  refine ⟨fun _ => ⟨_,Flow.code_2855,rfl,trivial⟩,?_⟩
  intro t ev u ins _ _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2855)
  cases hf.2

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control

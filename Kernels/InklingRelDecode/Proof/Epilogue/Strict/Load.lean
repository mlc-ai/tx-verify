-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Addr
public import Lemmas.Flow.StepsQFT
import Kernels.InklingRelDecode.Flow.Code.Part044

@[expose] public section

/-! # The strict step of the tensor memory load of the accumulator row -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value} {R : TState → Prop} {Wf : Event → Prop}

theorem off_load {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hc : kernel.code[2607]? = some ⟨none, .tcLd ds ta sh⟩) :
    ∀ r ∈ ctlLive 2607, r ∉ ds := by
  have h := hc.symm.trans Flow.code_2607
  simp only [Option.some.injEq, Instr.mk.injEq, Op.tcLd.injEq, true_and] at h
  obtain ⟨rfl, rfl, -⟩ := h
  decide +kernel

/-- **The load** returns data words of four bytes (`hD`, from the well-formedness of the event). -/
theorem sstep_load
    (hD : ∀ ev, Wf ev → ev.pc = 2607 → ∀ a vals sh, ev.kind = .tc (.ld a vals sh) →
      ∀ x ∈ vals, Dat32 x) (ev : Event) :
    (code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) Wf ⟨.load, v⟩ ev := by
  refine Code.tcLdFP (C := code e L g) (d := ⟨.load, v⟩) (f := fun _ => ⟨.waitLd, v⟩)
    Flow.code_2607 (fun _ h => by cases h)
    (by change Assumptions.all.any (·.tcLdWait 2607) = false; decide +kernel)
    (by decide +kernel) ?_ (fun ev hw hpc a vals hk => hD ev hw hpc a vals _ hk)
    (fun _ _ => rfl) rfl rfl (by change afterF lateQt 2607 _ = true; decide +kernel)
    (fun hinv _ _ _ => ⟨rfl, rfl, trivial, seg_step (s' := .waitLd) (v := v) (p := 2607) rfl
      (by decide +kernel)⟩) ev
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  exact off_load Flow.code_2607 r hr

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict

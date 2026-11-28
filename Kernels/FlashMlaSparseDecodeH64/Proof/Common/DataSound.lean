-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataState
public import Lemmas.Flow.GlueU
public import Lemmas.Flow.CountedU
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Gen.DataSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSteps

@[expose] public section

/-! # The value thread machine is sound (UB-tolerant)

`threadD_sound`: `threadD` follows every launched thread as `thread` does (`thread_sound`), from
the same startup and hand-offs; a value slot adds its machine's steps (`<role>D_steps`) and its
first state from its control machine's (`<role>D_start`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **Slot `Dequant` (values)**: the data machine's steps, from the control machine's
(`Over.stepAtU`, `Dequant.Data.dataStep_all`). -/
theorem dequantD_steps (hp : Pre P L m) :
    ∀ d, (dequantDCode P L g (warpW L g)).StepAtU d := fun d =>
  (Dequant.Data.over P L g _).stepAtU (frag_stepsU hp (.inl .dequant))
    (Dequant.Data.dataStep_all d)

/-- **Slot `Dequant` (values)**: its first state from the control machine's. -/
theorem dequantD_start {w : BitVec 64} {t : TState}
    (h : (dequantCode P L g w).AtD (dequantCode P L g w).init t) :
    (dequantDCode P L g w).AtD (dequantDCode P L g w).init t ∧
      (dequantDCode P L g w).inv (dequantDCode P L g w).init := by
  obtain ⟨hpc, hsub, hacc, hf, hF⟩ := h
  refine ⟨⟨hpc, hsub, hacc, hf, ?_⟩, Nat.one_pos⟩
  change Holds t.regs (_ ++ Dequant.Data.dF _ _ _)
  rw [holds_append]
  exact ⟨hF, trivial⟩

/-- **Slot `Wg0` (values)**: the data machine's steps, from the control machine's
(`Over.stepAtU`, `Wg0.Data.stepAtU`). -/
theorem wg0D_steps (hp : Pre P L m) : ∀ d, (wg0DCode P L g (warpW L g)).StepAtU d :=
  Wg0.Data.stepAtU hp (frag_stepsU hp (.inl .wg0))

/-- **Slot `Wg0` (values)**: its first state from the control machine's. -/
theorem wg0D_start {t : TState}
    (h : (wg0Code P L g (warpW L g)).AtD (wg0Code P L g (warpW L g)).init t ∧
      (wg0Code P L g (warpW L g)).inv (wg0Code P L g (warpW L g)).init) :
    (wg0DCode P L g (warpW L g)).AtD (wg0DCode P L g (warpW L g)).init t ∧
      (wg0DCode P L g (warpW L g)).inv (wg0DCode P L g (warpW L g)).init := by
  obtain ⟨⟨hpc, hsub, hacc, hf, hF⟩, hi⟩ := h
  refine ⟨⟨hpc, hsub, hacc, hf, ?_⟩, hi⟩
  change Holds t.regs (_ ++ Wg0.Data.dF _ _)
  rw [holds_append]
  exact ⟨hF, trivial⟩

/-- The value fragments' steps, the stubs' included. -/
theorem fragD_stepsU (hp : Pre P L m) :
    ∀ j d, (Code.withStubs (fragD P L g) Entry.pc j).StepAtU d
  | .inl .wg0, d => wg0D_steps hp d
  | .inl .dequant, d => dequantD_steps hp d
  | .inl .wg1, d => wg1_steps hp d
  | .inr r, d => (Code.stop_steps (entry_sites r) d).toStepAtU

/-- **The hand-offs of the startup** to the value fragments: the control hand-offs
(`thread_handoff`) and each slot's first state. -/
theorem threadD_handoff :
    Code.Handoff (startupCode P L g) (Code.withStubs (fragD P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) := by
  intro d j t hx hat hi
  have hc := thread_handoff (P := P) (L := L) (g := g) d j t hx hat hi
  cases j with
  | inl r =>
    cases r with
    | wg0 => exact wg0D_start hc
    | wg1 => exact hc
    | dequant => exact dequantD_start (w := warpW L g) hc.1
  | inr r => exact hc

/-- **The value thread machine of every launched thread is sound**, through any final undefined
behaviour. -/
theorem threadD_sound (hp : Pre P L m) : (threadD P L g).SoundU :=
  Code.counted_soundU (Code.glue_soundU (startup_start hp)
    (fun d hx => (startup_steps hp d hx).toStepAtU) (fragD_stepsU hp) threadD_handoff)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

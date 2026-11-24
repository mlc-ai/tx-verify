-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Safety
public import Lemmas.Kernel.Descent
public import Lemmas.Async.NcReadOnly

@[expose] public section

/-! # `copy_ldg`: every maximal execution is complete

The kernel has no asynchronous, shuffle or barrier instruction, and a thread's first event is its
load or its exit: every pending thread of a maximal execution extends it
(`Descent.progress_of_plain`), so every maximal execution is complete. The `nc` read of `A[g]`
returns the launch content of the bytes it reads, which keeps `nc-read-only`
(`ncReadOnly_wf_snoc`). -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0}

/-- The kernel has no shuffle instruction. -/
theorem noShfl : kernel.NoShfl := rfl

/-- The kernel has no atomic read-modify-write instruction. -/
theorem noAtomic : kernel.NoAtomic := rfl

/-- A thread's first site is no barrier. -/
theorem init_not_bar {g : Nat} {ins : Instr}
    (hc : kernel.code[(code L A B N g).pc (code L A B N g).init]? = some ins) :
    ins.op.isBar = false := by
  by_cases hgN : g < N
  · simp only [code, hgN, ↓reduceIte, Site.pc] at hc
    rw [Flow.code_load_0] at hc
    cases hc
    rfl
  · simp only [code, hgN, ↓reduceIte, Site.pc] at hc
    rw [Flow.code_exit_0] at hc
    cases hc
    rfl

/-- **`ProgressGoal`.** -/
theorem progress_goal (hpre : Pre L A B N x mem0)
    (hthr : ∀ X, Consistent L kernel Nc mem0 X → ThreadFacts L A B N X)
    (hsafe : SafeGoal kernel Nc L mem0) : ProgressGoal kernel Nc L mem0 :=
  Descent.progress_of_plain noTma noShfl noAtomic (sound_all hpre) hsafe
    (fun X hX => (hthr X hX).tracked) (fun X hX _ _ _ _ => no_bar hpre hX (hthr X hX))
    (fun _ _ _ hc => init_not_bar hc) fun X _ hX e r he a ha => by
      simp only [List.mem_singleton] at ha
      subst ha
      exact ncReadOnly_wf_snoc (hX.asm Assumptions.ncInput (by simp))
        fun a bs hk _ => he a bs hk

end
end PTX.Kernels.CopyLdg.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaDiscipline

@[expose] public section

/-! # An MMA thread works on its cluster's leader CTA

The prologue routes an MMA warp of an odd CTA straight to the common exit (`Prologue.mmaStart`),
and no MMA step leaves the exit (`Mma.next_lead`): every MMA state reached is on the leader CTA or
in the exit (`mma_lead`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

theorem Prologue.next_mma_lead {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {m : Mma.D}
    (hn : Prologue.next L g p e = some (some (.inr (.mma m)))) : Mma.Lead L g m := by
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.mma.injEq] at hn)
  all_goals (try subst hn)
  all_goals simp only [Prologue.mmaStart, Mma.Lead, Loader.leader]
  all_goals by_cases h : g / L.block % 2 = 0 <;> simp [h]

/-- Every MMA state a thread reaches is on its cluster's leader CTA or in the common exit. -/
theorem mma_lead {L : Launch} {g : Nat} {es : List Event} {m : Mma.D}
    (h : (code L g).toMachine.after (some (code L g).init) es = some (some (.inr (.mma m)))) :
    Mma.Lead L g m := by
  refine Machine.after_induction (M := (code L g).toMachine)
    (fun σ _ => ∀ m, σ = some (.inr (.mma m)) → Mma.Lead L g m) ?_ ?_ es _ h m rfl
  · intro m hm
    cases hm
  · intro σ es e σ' hq hn m hm
    subst hm
    rcases σ with _ | (p | (l | m0 | s | c))
    · simp [Code.toMachine] at hn
    · exact Prologue.next_mma_lead hn
    all_goals simp only [Code.toMachine, code, Option.map_eq_some_iff] at hn
    all_goals obtain ⟨o, ho, h'⟩ := hn
    all_goals cases o <;> simp at h'
    subst h'
    exact Mma.next_lead (hq m0 rfl) ho

end

end PTX.Kernels.Fp16Gemm8192.Proof

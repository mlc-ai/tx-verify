-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Steps
public import Lemmas.Flow.ShflFor

@[expose] public section

/-! # The head's shuffle is strict for the words that are not the index warp's

`Wg1.stepFor_hsh`: the strict step (`Code.StepFor`) of the head's shuffle for an event whose
received word is not `7`. The words `4`, `5` and the idle code's reach their site by a strict
segment (`head_mma`, `head_tma`, `head_idle`); only the word `7`'s walk (`head_index`) is
tolerant. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The head's shuffle, strict for an event that received a word other than `7`.** -/
theorem stepFor_hsh (hp : Pre P L m) (e : Event)
    (h7 : ∀ md av bv cv x ok, e = ⟨Site.pc P L g .hsh, .shfl md av bv cv (.bits 32 x) ok⟩ →
      ¬ scmpi .eq .b x 7 = true) : (code P L g).StepFor .hsh e := by
  refine Code.step_shflFor (nv := fun v _ => dispatch v)
    (by code_lookup) (by fact_free) (by fact_free) (by decide) (fun _ _ _ _ _ _ => rfl) rfl rfl
    (fun v _ => dispatch_ne v) e ?_
  intro recv ok d' he hv
  obtain ⟨md, av, bv, cv, he⟩ := he
  simp only [dispatch] at hv
  split at hv
  · rename_i x
    have h7x := h7 md av bv cv x ok he
    by_cases c5 : scmpi .eq .b x 5 = true
    · simp [h7x, c5] at hv
      subst hv
      obtain ⟨n, h⟩ := head_tma (L := L) (g := g) x ok h7x c5
      exact ⟨fun _ => ⟨n, h⟩, rfl, rfl, fun _ => trivial⟩
    by_cases c4 : scmpi .ne .b x 4 = true
    · simp [h7x, c5, c4] at hv
      subst hv
      obtain ⟨n, h⟩ := head_idle hp x ok h7x c5 c4
      exact ⟨fun _ => ⟨n, h⟩, rfl, rfl, fun _ => trivial⟩
    · simp [h7x, c5, c4] at hv
      subst hv
      obtain ⟨n, h⟩ := head_mma (L := L) (g := g) x ok h7x c5 c4
      exact ⟨fun _ => ⟨n, h⟩, rfl, rfl, fun _ => trivial⟩
  · simp at hv

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1

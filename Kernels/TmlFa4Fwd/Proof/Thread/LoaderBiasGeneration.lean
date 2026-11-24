-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasParity

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The successful return acquire of the same per-buffer ordinal as a Bias expectation.
Its parity is the initialized free phase followed by alternating buffer generations. -/
theorem biasExpectationGenerationGuard {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g j : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (biasReadyObject l cta stage) 32768 1 true .cta) :
    let ordinal := arrivals (biasReadyObject l cta stage) ((X.tr g).take j)
    ∃ (k : Nat) (e : Event), X.get (g,k) = some e ∧
      e.kind = .wait (biasEmptyObject l cta stage) ((ordinal + 1) % 2) true true .cta ∧
      okPolls (biasEmptyObject l cta stage) ((X.tr g).take k) = ordinal ∧
      Resumes kernel X (g,k) (g,j) := by
  obtain ⟨pc, he⟩ := hIssue
  obtain ⟨_, _, hLoc⟩ := actualArriveOffsetIn hp hX he
  have hCta : cta = g / l.block := congrArg Loc.cta hLoc
  subst cta
  have hIssue : X.Arrive (g,j) (biasReadyObject l (g / l.block) stage) 32768 1 true .cta :=
    ⟨pc, he⟩
  have hWarp := biasExpectationIssuerWarp hp hX stage hIssue
  obtain ⟨k, e, phase, _, hGet, hKind, hOrdinal, hResume⟩ :=
    biasExpectationOrdinalGuard hp hX stage hIssue
  have hParity := biasEmptyPollParity hp hX stage hWarp hGet hKind
  rw [hOrdinal] at hParity
  rw [hParity] at hKind
  exact ⟨k, e, hGet, hKind, hOrdinal, hResume⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasGeneration

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The expectation and the two stage barriers belong to the issuing CTA. -/
theorem biasExpectationOwner {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g j : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (biasReadyObject l cta stage) 32768 1 true .cta) :
    cta = g / l.block := by
  obtain ⟨_, he⟩ := hIssue
  obtain ⟨_, _, hLoc⟩ := actualArriveOffsetIn hp hX he
  exact congrArg Loc.cta hLoc

/-- The chosen loader's return responses alternate with the initially free stage as seed. -/
theorem biasEmptySelectedAlternates {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta g j : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (biasReadyObject l cta stage) 32768 1 true .cta)
    (hClean : ∀ r ∈ X.objects (biasEmptyObject l cta stage),
      (∃ q ok, r.action = .pollParity q ok) → r.fault = none) :
    SelectedAlternates (objectThreadSelected g) (X.objects (biasEmptyObject l cta stage)) 1 := by
  have hWarp := biasExpectationIssuerWarp hp hX stage hIssue
  have hCta := biasExpectationOwner hp hX stage hIssue
  subst cta
  apply MbarRing.Poll.alternates hX hClean
  intro k _ q acq sc hPoll
  rw [biasEmptyPollParity hp hX stage hWarp hPoll rfl, Nat.mod_mod]

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

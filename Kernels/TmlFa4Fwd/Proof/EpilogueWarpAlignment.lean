-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ContinuingEvent
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals
public import Lemmas.Flow.WarpScan
public import Lemmas.Step.WarpShfl

@[expose] public section

namespace PTX

noncomputable section

theorem WarpOrdinals.zero (L : Launch) (X : Execution) (g : Nat) :
    WarpOrdinals L X g (fun _ => 0) 0 0 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable {L : Launch} {K : Kernel} {A : List Assumption}

/-- A terminated run already at its next shuffle supplies the observed event and the
post-shuffle cursor, with the ordinal taken from its actual trace prefix. -/
theorem Next.shuffle_at {X : Execution} {g pos : Nat} {t s : TState} {mode : ShflMode} {a : Value}
    {b c ordinal : Nat} {step : Value → Bool → TState}
    (hn : Next K A L g t s (.shfl mode a b c step)) (hr : Run K A L g t ((X.tr g).drop pos) none)
    (hCount : ((X.tr g).take pos).countP Execution.isShfl = ordinal) :
    ∃ recv ok, X.get (g, pos) = some ⟨s.pc, .shfl mode a b c recv ok⟩ ∧
      X.ShflK (g, pos) ordinal ∧ Run K A L g (step recv ok) ((X.tr g).drop (pos + 1)) none := by
  obtain ⟨e, u, he, hf, hRest⟩ := hn.continuing_at (by
    rintro e ⟨recv, ok, _, hNone⟩
    cases hNone) hr
  obtain ⟨recv, ok, rfl, ht⟩ := hf
  obtain rfl := Option.some.inj ht
  exact ⟨recv, ok, he, ⟨⟨_, _, _, _, _, _, _, he⟩, hCount⟩, hRest⟩

end
end PTX

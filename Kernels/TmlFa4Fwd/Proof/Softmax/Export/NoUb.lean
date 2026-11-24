-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.BiasSrc
public import Kernels.TmlFa4Fwd.Proof.SmWarp.ReadSources
import Kernels.TmlFa4Fwd.Proof.SmWarp.NoUb
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp

/-- A softmax lane avoids UB when the bias and score reads have the expected payloads. -/
theorem noUb_of_reads {p L m X g k e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hr : ReadPayloads X)
    (hw : Prologue.warpIndex L g < 8) (he : X.get (g,k) = some e) (f : Fault) :
    e.kind ≠ .ub f := by
  have hn := numSteps hp
  have hd := storeSafe hp
  have hs := smSrc_of_data_sites hp hX hn hd (smSrcRest_of_reads hp hX hr)
  exact noUb hp hX hn hd hs hw (Frame.lt_of_get hX he) rfl he f

open PTX.Proof PTX.Flow Softmax

/-- **Every score load of a followed softmax lane returns single-precision numbers.** -/
def ScorePayloads (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d n r j a vals sh pc, X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.softmax,d⟩,n)) →
    d.site = .sld r j → ∀ v ∈ vals, ∃ x, v = .float .f32 x

/-- The softmax warps' data sites, from the bias hand-off and the score loads. -/
theorem smSrcRest_of_scores {p L m X} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hBias : BiasReadHandoff p L X)
    (hScore : ScorePayloads p L X) : SmSrcRest p L X := by
  intro g k d n c e he hσ hJ
  cases hs : d.site with
  | bld b j =>
    simpa only [ExpectRest, hs] using expect_bias hp hX hBias he hσ hJ hs
  | sld r j =>
    simp only [ExpectRest, ExpectD, hs]
    intro a vals sh hk
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    exact hScore g k d n r j a vals sh pc he hσ hs
  | _ => simp only [ExpectRest, hs]

/-- **A softmax lane makes no undefined behaviour** when its score loads return numbers. -/
theorem noUb_of_scores {p L m X g k e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hBias : BiasReadHandoff p L X)
    (hScore : ScorePayloads p L X) (hw : Prologue.warpIndex L g < 8)
    (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f :=
  noUb hp hX (numSteps hp) (storeSafe hp) (smSrc_of_data_sites hp hX (numSteps hp) (storeSafe hp)
    (smSrcRest_of_scores hp hX hBias hScore)) hw (Frame.lt_of_get hX he) rfl he f

end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp

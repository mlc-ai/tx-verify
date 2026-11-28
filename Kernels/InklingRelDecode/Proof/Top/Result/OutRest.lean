-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Top.Result.Output
public import Kernels.InklingRelDecode.Proof.Top.Result.Lse
public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiRest
import Kernels.InklingRelDecode.Proof.Top.Result.OutFinal
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseZero

@[expose] public section

/-! # The output and LSE words are stored

The coverage and agreement of the stores (`out_rest`, `lse_rest`) with the load's word of
`Result.finalWord`, given the entry of the epilogue. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The entry of the epilogue** of every complete followed execution. -/
def Result.Entry (Q : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → Complete L X → Follow Q L X →
    EpiEntryFacts Q L X

/-- **Every word of `OPart` is stored.** -/
theorem Result.outputRest (hp : Pre Q L m) (entry : Result.Entry Q L m) :
    Result.Output.Words Q L m := by
  intro X hX hc hf r hr s hs tok ht h hh d hd
  exact out_rest hp hX hf hc (Result.notCanceled hX) (Protocol.Shared.base_read hp hX hf)
    (fun he hj v => Result.finalWord hp hX hc hf he hj v) hp.scalePos (entry X hX hc hf)
    r hr s hs tok ht h hh d hd

/-- **Every word of `LsePart` is stored.** -/
theorem Result.lseRest (hp : Pre Q L m) (entry : Result.Entry Q L m) :
    Result.Lse.Words Q L m := by
  intro X hX hc hf r hr s hs tok ht h hh
  exact lse_rest hp hX hf hc (Result.notCanceled hX) hp.scalePos (entry X hX hc hf)
    r hr s hs tok ht h hh

end PTX.Kernels.InklingRelDecode.Proof.Top

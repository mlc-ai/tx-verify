-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk3Upd

@[expose] public section

/-!
# The softmax value chain by iteration: the statements

The four default warps of a CTA are not at one synchronizing ordinal at one program point (warp 0
alone runs the allocation and `relinquish_alloc_permit`), so the facts that relate warps (the
scratch words, the barrier-0 ordinals) are stated by the loop iteration `i` of the softmax region
(`Sm.D.i`) and the CTA `c`:

* `DecAgree c j`: two default threads of CTA `c` at `shfl12` of iteration `j` take the same
  lazy-rescale decision (`Sm.D.p170` of the word their shuffle returned), in the form
  `p170_cta` concludes;
* `B0At c i`: two default threads of CTA `c` at `bar23` of iteration `i` have made the same number
  of barrier-0 events;
* `StoreUniform c i`: the 32 lanes of the default warp `r` of CTA `c` store at `store10` of
  iteration `i` one word `v r` (`D.stg.cm4`), which reads as a number that is not `+inf`;
* `ScratchIt i`: in iteration `i` of every CTA, the load `ldL` of every default thread returns a
  word that reads as the number `W r` of its scratch word `r = tid % 4`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section

variable {Q : Params} {L : Launch} {X : Execution}

/-- **The lazy-rescale decision of iteration `j` is the same in the default threads of CTA `c`.** -/
def DecAgree (Q : Params) (L : Launch) (X : Execution) (c j : Nat) : Prop :=
  ∀ {g g' k k' : Nat} {d d' : Sm.D} {e e' : Event}, g < L.threads → g' < L.threads →
    g / L.block = c → g' / L.block = c → X.get (g, k) = some e → X.get (g', k') = some e' →
    St Q L X g k = some (some (.d (.sm d))) → St Q L X g' k' = some (some (.d (.sm d'))) →
    d.site = .shfl12 → d'.site = .shfl12 → d.i = j → d'.i = j →
    ∃ (r r' : Value) (o o' : Bool), e = ⟨d.site.pc, .shfl .bfly d.stg.m2 1 31 r o⟩ ∧
      e' = ⟨d'.site.pc, .shfl .bfly d'.stg.m2 1 31 r' o'⟩ ∧ d.p170 r = d'.p170 r'

/-- **The default threads of CTA `c` at `bar23` of iteration `i` have made the same number of
barrier-0 events.** -/
def B0At (Q : Params) (L : Launch) (X : Execution) (c i : Nat) : Prop :=
  ∀ {g g' k k' : Nat} {d d' : Sm.D}, g < L.threads → g' < L.threads →
    g / L.block = c → g' / L.block = c →
    St Q L X g k = some (some (.d (.sm d))) → St Q L X g' k' = some (some (.d (.sm d'))) →
    d.site = .bar23 → d'.site = .bar23 → d.i = i → d'.i = i →
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      ((X.tr g').take k').countP (Execution.isBarId 0)

/-- **The scratch words of iteration `i` read as numbers**, for every default thread of every
CTA, at any ordinal. -/
def ScratchIt (Q : Params) (L : Launch) (X : Execution) (i : Nat) : Prop :=
  ∀ c : Nat, ∃ W : Nat → EReal, (∀ r, W r ≠ ⊤) ∧
    ∀ {g k : Nat} {d : Sm.D}, g < L.threads → g / L.block = c →
      St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl11 → d.i = i →
      ReadsAs d.stg.ld (W (g % L.block % 4))

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

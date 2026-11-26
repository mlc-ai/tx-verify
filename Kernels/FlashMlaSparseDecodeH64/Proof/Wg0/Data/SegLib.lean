-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Lemmas.Flow.SegDead
public import Lemmas.Flow.RunFrame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine

@[expose] public section

/-! # Strict run windows: the shared lemmas

A window of data registers only is a chain of value runs between two events. `windowS_close` turns
the chain, framed over the control facts `Hc'` of the successor, into the exact segment from the
control facts `Hc` and the data facts to the successor's, under the runs' condition. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem windowS_snd {R : Nat → Option Value} {A B : List (Nat × Value)}
    (h : Holds R (A ++ B)) : Holds R B := ((holds_append _ _ _).mp h).2

/-- **A framed run chain as an exact segment.** -/
theorem windowS_close {K : Kernel} {A : List Assumption} {L : Launch} {g n s b : Nat}
    {C : Prop} {Hc Hc' F Fr G Gr : List (Nat × Value)}
    (h : SegD K A L g n s (Fr ++ Hc') b (Gr ++ Hc') C) (hC : C)
    (hF : ∀ R, Holds R (Hc ++ F) → Holds R Fr) (hsub : ∀ R, Holds R Hc → Holds R Hc')
    (hG : ∀ R, Holds R Gr → Holds R G) : ∃ n, Seg K A L g n s (Hc ++ F) b (Hc' ++ G) := by
  refine ⟨n, ((h.seg hC).weaken_end fun R hR => ?_).weaken_start fun R hR => ?_⟩
  · have hs := (holds_append _ _ _).mp hR
    exact (holds_append _ _ _).mpr ⟨hs.2, hG R hs.1⟩
  · have hs := (holds_append _ _ _).mp hR
    exact (holds_append _ _ _).mpr ⟨hF R hR, hsub R hs.1⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.IpTmZero

@[expose] public section

/-!
# The epilogue's Tensor Memory base is 0

`Interface.tmz_inv` (from `BaseWordRead`) says the base word a default-partition thread holds is 0
at every state after the common start's load: `TmZ (.d (.epi d))` is `d.pr.tm = 0`. So the premise
`Rs.OSrcPrem.epiTm` (the epilogue's `d.pr.tm = 0`) is `epiTm_of`, by the argument of
`smBaseZero_of` (a state beyond the end of the trace is the last state).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The epilogue's base word is 0** at every state of a launched thread, if every read of the
base word returns the zero word. -/
theorem epiTm_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) :
    ∀ {g k : Nat} {d : Epi.D}, g < L.threads → St Q L X g k = some (some (.d (.epi d))) →
      d.pr.tm = 0 := by
  intro g k d hg hσ
  by_cases hk : k ≤ (X.tr g).length
  · exact tmz_inv hpre hX hf hb hg k _ hk hσ
  · have h2 : St Q L X g (X.tr g).length = some (some (.d (.epi d))) :=
      (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k) (by omega)).symm.trans hσ
    exact tmz_inv hpre hX hf hb hg _ _ le_rfl h2

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

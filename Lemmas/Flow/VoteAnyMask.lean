-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # The member mask of a `vote.any`

A successful `vote.sync.any` records the member mask its mask operand reads (`fires_voteAnyU`
forgets it). -/

namespace PTX.Flow
open PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **A successful `vote.any` with mask operand reading `bits`** records the mask `bits`. -/
theorem fires_voteAnyU_mask {t u : TState} {pc dv pr : Nat} {neg : Bool} {ty : Option DType}
    {mask : Opnd} {e : Event} {bits : BitVec 64} (hm : readBits L g t 32 mask = .ok bits)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.vote .any neg, ty, [some dv], [.reg pr],
      some mask⟩)) e (some u)) :
    ∃ p r, e = ⟨pc, .voteMode .any bits.toNat p r⟩ := by
  have hw : warpTmpl L g t ⟨.vote .any neg, ty, [some dv], [.reg pr], some mask⟩ =
      voteModeTmpl L g t .any dv pr neg mask := rfl
  simp only [eventTmpl, hw, voteModeTmpl, hm] at hf
  cases hp : readPred L g t (.reg pr) with
  | error f => simp only [hp, Fires] at hf; cases hf.2
  | ok pred =>
    simp only [hp] at hf
    split at hf
    · split at hf
      · obtain ⟨r, he, -⟩ := hf
        exact ⟨_, r, he⟩
      · cases hf.2
    · cases hf.2

end PTX.Flow

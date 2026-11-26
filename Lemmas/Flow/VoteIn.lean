-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # The predicate a `vote.any` records

A `vote.any` whose predicate register holds `.pred b` records the input `b != neg` (Core's
`voteModeTmpl`): `fires_voteAnyU_in`. -/

namespace PTX.Flow
open PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem fires_voteAnyU_in {t : TState} {o : Option TState} {pc dv pr : Nat}
    {neg b : Bool} {ty : Option DType}
    {mask : Opnd} {e : Event} (hu : ∀ f, e.kind ≠ .ub f) (hr : t.regs pr = some (.pred b))
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.vote .any neg, ty, [some dv], [.reg pr],
      some mask⟩)) e o) :
    ∃ m r, e = ⟨pc, .voteMode .any m (b != neg) r⟩ := by
  have hw : warpTmpl L g t ⟨.vote .any neg, ty, [some dv], [.reg pr], some mask⟩ =
      voteModeTmpl L g t .any dv pr neg mask := rfl
  have hp : readPred L g t (.reg pr) = .ok b := by
    simp [readPred, readReg, hr, pure, Except.pure]
    rfl
  simp only [eventTmpl, hw, voteModeTmpl] at hf
  cases hm : readBits L g t 32 mask with
  | error f => simp only [hm, Fires] at hf; exact absurd (by rw [hf.1]) (hu _)
  | ok m =>
    simp only [hm, hp] at hf
    split at hf
    · split at hf
      · obtain ⟨r, he, -⟩ := hf
        exact ⟨_, r, he⟩
      · simp only [Fires] at hf
        exact absurd (by rw [hf.1]) (hu _)
    · simp only [Fires] at hf
      exact absurd (by rw [hf.1]) (hu _)

end PTX.Flow

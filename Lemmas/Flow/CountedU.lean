-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Counted

@[expose] public section

namespace PTX.Flow.Code
noncomputable section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
  {C : Code K A L g} {κ : Type} {cls : κ → Event → Bool}

/-- **The step obligations of the counted machine** are those of `C`. -/
theorem counted_stepsU {d : C.D} (h : C.StepAtU d) (n : κ → Nat) :
    (C.counted cls).StepAtU (d, n) where
  site := h.site
  step := by
    intro t e u ins hat hinv hc hf
    rcases h.step ins hat hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
    · exact .inl (.inl (by rw [counted_next, hn]; rfl))
    · exact .inl (.inr ⟨(d', bump cls n e), t', by rw [counted_next, hn]; rfl, hl, hg⟩)
    · exact .inr ⟨by rw [counted_next, hn]; rfl, hd⟩

/-- **The counted machine of a sound machine is sound.** -/
theorem counted_soundU (hC : C.SoundU) : (C.counted cls).SoundU where
  start := hC.start
  steps := fun d => counted_stepsU (hC.steps d.1) d.2

end
end PTX.Flow.Code

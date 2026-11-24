-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Glue

@[expose] public section

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

namespace Code

variable {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}

/-- **The step obligations of the glued machine.** -/
theorem glue_stepsU (hP : ∀ d, exit d = none → P.StepAtU d) (hR : ∀ i d, (R i).StepAtU d)
    (hglue : Handoff P R exit) : ∀ d, (glue P R exit).StepAtU d := by
  intro d
  cases d with
  | inl d =>
    by_cases hx : exit d = none
    · have hs := hP d hx
      refine ⟨fun hinv => hs.site hinv.1, ?_⟩
      intro t e u ins hat hinv hc hf
      rcases hs.step ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by show (P.next d e).map _ = _; rw [hn]; rfl))
      · exact .inl (.inr ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl,
          hl, hg.imp (good_enter hglue) id⟩)
      · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩
    · -- an exit state of the first fragment is no state of the glued machine's runs: its
      -- invariant is false
      exact ⟨fun hinv => absurd hinv.2 hx, fun _ _ hinv => absurd hinv.2 hx⟩
  | inr s =>
    obtain ⟨i, d⟩ := s
    have hs := hR i d
    refine ⟨hs.site, ?_⟩
    intro t e u ins hat hinv hc hf
    rcases hs.step ins hat hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
    · exact .inl (.inl (by show ((R i).next d e).map _ = _; rw [hn]; rfl))
    · exact .inl (.inr ⟨.inr ⟨i, d'⟩, t', by show ((R i).next d e).map _ = _; rw [hn]; rfl,
        hl, hg⟩)
    · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩

/-- **The glued machine is sound.** -/
theorem glue_soundU
    (hstart : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ P.AtD P.init t ∧ P.inv P.init)
    (hP : ∀ d, exit d = none → P.StepAtU d) (hR : ∀ i d, (R i).StepAtU d)
    (hglue : Handoff P R exit) : (glue P R exit).SoundU where
  start := by
    obtain ⟨t, hl, ha, hi⟩ := hstart
    exact ⟨t, hl, good_enter hglue ⟨ha, hi⟩⟩
  steps := glue_stepsU hP hR hglue

end Code
end
end PTX.Flow

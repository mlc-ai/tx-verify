-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LoopGlue
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Roles

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section

open PTX PTX.Flow PTX.Proof PTX.Flow.Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}


variable {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}
  {back : (i : ι) → (R i).D → Option P.D}

/-- **The UB-tolerant step obligations of the loop glue.** -/
theorem loopGlue_stepsU (hP : ∀ d, exit d = none → P.StepAtU d)
    (hR : ∀ i d, back i d = none → (R i).StepAtU d) (hglue : Handoff P R exit)
    (hback : Back P R back) (hinit : ∀ i, back i (R i).init = none) :
    ∀ d, (loopGlue P R exit back).StepAtU d := by
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
          hl, hg.imp (good_enter_loop hglue hinit) id⟩)
      · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩
    · exact ⟨fun hinv => absurd hinv.2 hx, fun _ _ hinv => absurd hinv.2 hx⟩
  | inr s =>
    obtain ⟨i, d⟩ := s
    by_cases hb : back i d = none
    · have hs := hR i d hb
      refine ⟨fun hinv => hs.site hinv.1, ?_⟩
      intro t e u ins hat hinv hc hf
      rcases hs.step ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by show ((R i).next d e).map _ = _; rw [hn]; rfl))
      · exact .inl (.inr ⟨backEnter P R exit back i d', t',
          by show ((R i).next d e).map _ = _; rw [hn]; rfl, hl,
          hg.imp (good_backEnter hglue hback hinit) id⟩)
      · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩
    · exact ⟨fun hinv => absurd hinv.2 hb, fun _ _ hinv => absurd hinv.2 hb⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Lib

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Init
public import Lemmas.Kernel.Safety.TableU

@[expose] public section
namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

variable (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X) (hT : T.ShapeOkU S)
  (hF : T.Followed X S)
include hC hX hT hF

theorem RoleTable.noMbarUninitU
    (hpub : ∀ g k d e m, S g → stateAt C X g k = some (some d) → T.J g d → (C g).inv d →
      T.Ev g d e → X.get (g, k) = some e → MbarOf e m → (∀ c, e.kind ≠ .mbInit m c) →
      ∃ i count, X.MbInit i m count ∧ InitPublished L X i (g, k) m)
    (hout : ∀ i m, X.UsesMbar i m → ¬ S i.1 → (∀ count, ¬ X.MbInit i m count) →
      ∃ j count, X.MbInit j m count ∧ InitPublished L X j i m) :
    ¬ MbarUninit L X := by
  rintro ⟨⟨g, k⟩, m, hu, hni, hno⟩
  by_cases hg : S g
  · obtain ⟨e, he, hm⟩ := usesMbar_mbarOf hu
    have hub : ∀ f, e.kind ≠ .ub f := by
      obtain ⟨pc, kd⟩ := e
      rintro f rfl
      simp only [MbarOf] at hm
    obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.ev_of_ne_ubU hC hX hT hF hg he hub
    exact hno (hpub g k d e m hg hσ hJ hi hev he hm (usesMbar_not_init he hni))
  · exact hno (hout _ m hu hg hni)

end

end PTX.Frame

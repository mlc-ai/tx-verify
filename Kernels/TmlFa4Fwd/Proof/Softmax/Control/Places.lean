-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

variable {p : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}

/-- The control projection of the place table, including the elected lane's edge. -/
def PlaceStep (L : Launch) (g : Nat) (d d' : Softmax.D) (e : Event) : Prop :=
  (d'.site = d.site ∧ NoCls d e) ∨
    (d'.site ∈ nexts (lz L g) d.site ∧
      (d.site.isPel = true → ∀ m inst ld, e.kind = .elect m inst ld →
        (d'.site.isParr2 = true ↔ laneOf L g = ld)))

theorem succ_places (hn : succ p L g d e = some (some d')) :
    PlaceStep L g d.scheduler d'.scheduler e := by
  have direct (h : (Softmax.succ p L g d.scheduler e).map (Option.map erase) = some (some d')) :
      PlaceStep L g d.scheduler d'.scheduler e := by
    obtain ⟨x,hx,hm⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨a,rfl,rfl⟩ := Option.map_eq_some_iff.mp hm
    rcases Softmax.succ_cases hx with ⟨hs,-,-,hc⟩ | hM
    · exact .inl ⟨hs,hc⟩
    · obtain ⟨hs, _, _, _, _, _, _, hc⟩ := hM
      exact .inr ⟨hs, hc⟩
  obtain ⟨s,v,k,acc⟩ := d
  cases s with
  | sld r c =>
    simp only [succ] at hn
    split at hn
    · cases r <;> cases hn <;> apply Or.inr <;> refine ⟨?_, nofun⟩
      all_goals simp [D.scheduler, nexts]
      all_goals split <;> simp
    · cases hn
  | bld b c =>
    simp only [succ] at hn
    split at hn
    · rename_i a bs hk
      split at hn
      · cases hn
        exact .inl ⟨rfl,.inr (.inl ⟨a,bs,hk⟩)⟩
      · cases hn
        refine .inr ⟨?_,nofun⟩
        simp only [D.scheduler, nexts]
        split <;> simp
    · cases hn
  | _ => exact direct hn

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Readback
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow
set_option maxRecDepth 100000

/-- Sites between the score poll and the closing poll. -/
def body : Site → Bool
  | .sld .. | .sldw .. | .wb .. | .bld .. | .fence .. | .bsync .. | .barr .. | .stat ..
  | .narr .. | .pst .. | .pwst .. | .parr .. | .pws .. | .pel .. | .parr2 .. => true
  | _ => false

/-- A score chunk and a bias chunk can be overwritten only by their own load sites. -/
theorem chunk_frame {p L g} {d d' : D} {e : Event} (h : succ p L g d e = some (some d'))
    (inside : body d.site = true) (c : Fin 4) (b : Fin 16) :
    (∀ r, d.site ≠ .sld r c) → (∀ z, d.site ≠ .bld z b) →
    d'.v.sv c = d.v.sv c ∧ d'.v.bk b = d.v.bk b ∧ d'.v.br b = d.v.br b := by
  intro hs hb
  obtain ⟨s,v,k,acc⟩ := d
  cases s with
  | sld r j =>
    have ne : c ≠ j := fun eq => hs r (by rw [eq])
    cases r <;> sc_split <;> exact ⟨Function.update_of_ne ne _ _,rfl,rfl⟩
  | bld z j =>
    have ne : b ≠ j := fun eq => hb z (by rw [eq])
    sc_split <;> first | exact ⟨rfl,rfl,rfl⟩ |
      exact ⟨rfl,Function.update_of_ne ne _ _,Function.update_of_ne ne _ _⟩
  | pst r q =>
    cases r <;> (match q with | 0 | 1 | 2 | 3 => ?_) <;> sc_split <;> exact ⟨rfl,rfl,rfl⟩
  | sldw _ | wb _ | fence _ | bsync _ | barr _ | stat _ | narr _ | pwst _ _ | parr _
    | pws _ | pel _ | parr2 _ => sc_split <;> exact ⟨rfl,rfl,rfl⟩
  | _ => cases inside

theorem score_frame {p L g d d' e} (hn : succ p L g d e = some (some d'))
    (inside : body d.site = true) (c : Fin 4) (other : ∀ r, d.site ≠ .sld r c) :
    d'.v.sv c = d.v.sv c := by
  by_cases h : ∃ z b, d.site = .bld z b
  · obtain ⟨z,b,eq⟩ := h
    have diff : b ≠ b+1 := by omega
    exact (chunk_frame hn inside c (b+1) other
      (fun _ e => diff ((Site.bld.inj (eq.symm.trans e)).2))).1
  · exact (chunk_frame hn inside c 0 other (fun z e => h ⟨z,0,e⟩)).1

theorem bias_frame {p L g d d' e} (hn : succ p L g d e = some (some d'))
    (inside : body d.site = true) (b : Fin 16) (other : ∀ z, d.site ≠ .bld z b) :
    d'.v.bk b = d.v.bk b ∧ d'.v.br b = d.v.br b := by
  by_cases h : ∃ r c, d.site = .sld r c
  · obtain ⟨r,c,eq⟩ := h
    have diff : c ≠ c+1 := by omega
    exact (chunk_frame hn inside (c+1) b
      (fun _ e => diff ((Site.sld.inj (eq.symm.trans e)).2)) other).2
  · exact (chunk_frame hn inside 0 b (fun r e => h ⟨r,0,e⟩) other).2

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data

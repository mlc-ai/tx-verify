-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.RefNext

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

theorem scheduler_ref {p L g d n} (h : Ref p L g (d,n)) :
    Correction.Ref p L g (d.scheduler,n) := by
  refine ⟨h, fun st _ => ?_⟩
  fin_cases st <;> exact le_refl (0 : ℝ)

/-- A protocol successor cannot stop on the shape, sign, or payload of a statistics or TMEM
read. Scheduler control words retain their existing reference-source contract. -/
theorem not_stop {p L g d e n} (hJ : Ref p L g (d,n)) (hE : Expect d e) :
    succ p L g d e ≠ some none := by
  have base (hs : ExpectD d.scheduler e) :
      ((Correction.succ p L g d.scheduler e).map (Option.map erase)) ≠ some none := by
    intro h
    obtain ⟨s, hs', hx⟩ := Option.map_eq_some_iff.mp h
    cases s with
    | none => exact Correction.not_stop (scheduler_ref hJ) hs hs'
    | some s => cases hx
  obtain ⟨s,v,k⟩ := d
  cases s with
  | rscale st | fsum st | fmax st | rld st c | fld st j =>
    simp only [succ]
    split <;> intro h <;> cases h
  | fdone st i =>
    fin_cases st <;> fin_cases i
    · exact base trivial
    · exact base trivial
    · exact base trivial
    · exact fun h => by cases h
  | lse i =>
    fin_cases i
    · exact fun h => by cases h
    · exact base trivial
  | word | down | up | total | vote | pre | tiles | q0 | q1 | uk => exact base hE
  | _ => exact base trivial

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

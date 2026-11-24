-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Ref
import Kernels.TmlFa4Fwd.Proof.Softmax.RefNext

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

/-- The scheduler expectations suffice to prevent a stop on any event. -/
theorem not_stop {p L g d e n} (hJ : Ref p L g (d,n)) (hE : Expect p L g d e) :
    succ p L g d e ≠ some none := by
  have base (hs : ExpectD p L g d.scheduler e) :
      (Softmax.succ p L g d.scheduler e).map (Option.map erase) ≠ some none := by
    intro h
    obtain ⟨s, hs', hx⟩ := Option.map_eq_some_iff.mp h
    cases s with
    | none => exact Softmax.not_stop hJ hs hs'
    | some s => cases hx
  obtain ⟨s,v,k,acc⟩ := d
  cases s with
  | sld r c =>
    simp only [succ]
    split
    · cases r <;> intro h <;> cases h
    · intro h; cases h
  | bld b c =>
    simp only [succ]
    split
    · split <;> intro h <;> cases h
    · intro h; cases h
  | _ => exact base hE

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

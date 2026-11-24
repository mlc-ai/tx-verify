-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepAt
import Kernels.TmlFa4Fwd.Proof.Softmax.Handoff
import Kernels.TmlFa4Fwd.Proof.Softmax.Steps

@[expose] public section

/-! # The softmax warps' machine meets its step obligations -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **Every state of the role's machine meets its step obligation.** -/
theorem stepAt (hp : Pre p L m) (hg : g < L.threads) (d : D) : (codeT p L g).StepAt d where
  site := fun ⟨hi, hw, hn⟩ => by
    have hS : (codeD p L g).StepAt d := by
      rcases hn with hN | hn
      · exact Softmax.stepAt hp hg hw (hN g hg hw) d
      · exact stepAt_ctl hp hg hw d hn
    exact hS.site hi
  step := fun {t e u} ins hat ⟨hi, hw, hn⟩ hc hf => by
    have hS : (codeD p L g).StepAt d := by
      rcases hn with hN | hn
      · exact Softmax.stepAt hp hg hw (hN g hg hw) d
      · exact stepAt_ctl hp hg hw d hn
    have hgood : ∀ d' t', d'.numeric = false ∨ NumAll p L → (codeD p L g).Good (some d') t' →
        (codeT p L g).Good (some d') t' := fun d' t' hn' ⟨ha, hi'⟩ =>
      ⟨ha, hi', hw, hn'.symm⟩
    by_cases hN : NumAll p L
    · rw [show (codeT p L g).next d e = (codeD p L g).next d e from next_eq hN d e]
      rcases hS.step ins hat hi hc hf with (h | ⟨d', t', h, hl, hG⟩) | h
      · exact .inl (.inl h)
      · exact .inl (.inr ⟨d', t', h, hl, hgood d' t' (.inr hN) hG⟩)
      · exact .inr h
    · have hx : (codeT p L g).next d e = redirect ((codeD p L g).next d e) := by
        simp only [codeT, nextT, hN, ↓reduceIte]
      rw [hx]
      rcases hS.step ins hat hi hc hf with (h | ⟨d', t', h, hl, hG⟩) | ⟨h, hd⟩
      · rw [h]; exact .inl (.inl rfl)
      · rw [h]
        by_cases hd' : d'.numeric = true
        · simp only [redirect, hd', ↓reduceIte]; exact .inl (.inl trivial)
        · simp only [redirect, hd', Bool.false_eq_true, ↓reduceIte]
          exact .inl (.inr ⟨d', t', rfl, hl, hgood d' t' (.inl (by simpa using hd')) hG⟩)
      · rw [h]; exact .inr ⟨rfl, hd⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ShflOps

@[expose] public section

/-! # What a shuffle instruction fires

A `shfl.sync` fires a shuffle event or undefined behaviour (`fires_shflTmpl_kind`), whatever its
operands read. -/

namespace PTX.Flow
open PTX

variable {L : Launch} {g : Nat} {t : TState}

theorem fires_shflTmpl_kind {mode : ShflMode} {d : Nat} {p : Option Nat} {a b c mask : Opnd}
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (shflTmpl L g t mode d p a b c mask) e o) :
    (∃ av bv cv recv ok, e.kind = .shfl mode av bv cv recv ok) ∨ ∃ f, e.kind = .ub f := by
  unfold shflTmpl at hf
  split at hf
  · split_ifs at hf
    · obtain ⟨recv, ok, h, -⟩ := hf
      exact .inl ⟨_, _, _, recv, ok, by rw [h]⟩
    all_goals exact .inr ⟨_, by rw [hf.1]⟩
  all_goals exact .inr ⟨_, by rw [hf.1]⟩

end PTX.Flow

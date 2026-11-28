-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.Step.LoadVec
import Lemmas.Flow.Events

@[expose] public section

/-! # A scalar load that does not fault is a read of a 32-bit word

A non-undefined-behaviour event of a scalar load is a read, and when the bytes read are those of
a 32-bit word the read rebuilds. -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem read_live {pc : Nat} {ins : Instr} {a : MemAccess} {t : TState}
    {o : Option TState} {v : Event} (hop : ins.op = .mem a) (hk : a.kind = .load)
    (hnc : a.nc = false) (hsp : a.locSpace? = none)
    (hf : Fires pc (eventTmpl A L g t ins.op) v o) (hu : ∀ f, v.kind ≠ .ub f)
    (rebuilds : ∀ ac bs, v.kind = .rd ac bs → ∃ x, rebuild 3 bs = .ok x) :
    ∃ ac bs, v.kind = .rd ac bs ∧ (rebuild 3 bs).toOption.isSome = true := by
  rw [hop] at hf
  refine shape_cont (P := fun e => (∀ f, e.kind ≠ .ub f) →
    (∀ ac bs, e.kind = .rd ac bs → ∃ x, rebuild 3 bs = .ok x) →
    ∃ ac bs, e.kind = .rd ac bs ∧ (rebuild 3 bs).toOption.isSome = true) hf
    ⟨nofun, nofun⟩ ?_ (fun f hu' => absurd rfl (hu' f)) hu rebuilds
  intro u hf' hu' rebuilds'
  obtain ⟨ac, bs, rfl, -⟩ := Code.fires_accessLoad hk hnc hsp hf'
  obtain ⟨x, hx⟩ := rebuilds' ac bs rfl
  exact ⟨ac, bs, rfl, by rw [hx]; rfl⟩

end PTX.Flow

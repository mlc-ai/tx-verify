-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataLoad

@[expose] public section

/-! # The data step of a guarded load

`DataStep.load` for a load with a guard (the event fired), the data step reads the loaded value
from the event. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of a one-register load with a guard**: from the state after it (bytes that do
not rebuild fault). -/
theorem DataStep.loadG {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {gd : Option (Nat × Bool)} {a : MemAccess} {r : Nat}
    (hc : K.code[C'.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (he : a.ext = .same) (hr : a.regs = [r]) (hs : C'.inv d → C'.sub d = 0)
    (ha : C'.inv d → C'.acc d = [])
    (hrun : C'.inv d → ∀ x bs v d' t, rebuild 3 bs = .ok v →
      C'.next d ⟨C'.pc d, .rd x bs⟩ = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } t' → Stops K A L g t' →
        Holds t'.regs (dF d')) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  rw [hr]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr (Machine.dead_of_fault (K := K) (A := A) (L := L) (g := g) (f := f)
      (u := afterLoad t [r] bs) (by simp only [afterLoad, hv]))
  | ok v =>
    rw [afterLoad_ok (hat.2.1.trans (hs hi)) (hat.2.2.1.trans (ha hi)) hv]
    exact hrun hi x bs v d' t hv hn hat

end
end PTX.Flow.Code

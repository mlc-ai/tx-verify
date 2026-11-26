-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReachSegU

@[expose] public section

/-! # The data step of a scalar `.nc` load, with the loaded word

`DataStep.loadNc` hands the continuation the loaded value `v` but not that the event's bytes
rebuild to it. `DataStep.loadNcV` also gives `rebuild 3 bs = .ok v`, so a data machine can state
the loaded register's fact from the event's payload. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of a scalar `.nc` load** with the rebuilt word named. -/
theorem DataStep.loadNcV {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {a : MemAccess} {r base w : Nat} {sp : Space}
    (hc : K.code[C'.pc d]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r]) (hs : C'.inv d → C'.sub d = 0)
    (ha : C'.inv d → C'.acc d = [])
    (hrun : C'.inv d → ∀ x bs v, rebuild 3 bs = .ok v → ∀ d' t,
      C'.next d ⟨C'.pc d, .nc x bs⟩ = some (some d') → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } t' → Stops K A L g t' →
        Holds t'.regs (dF d')) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g)
        { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  rw [hr]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr (Machine.dead_of_fault (K := K) (A := A) (L := L) (g := g) (f := f)
      (u := afterLoad t [r] bs) (by simp only [afterLoad, hv]))
  | ok v =>
    rw [afterLoad_ok (hat.2.1.trans (hs hi)) (hat.2.2.1.trans (ha hi)) hv]
    exact hrun hi x bs v hv d' t hn hat

end
end PTX.Flow.Code

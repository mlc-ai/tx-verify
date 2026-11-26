-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NcLoadU

@[expose] public section

/-! # A scalar `.nc` load whose value the control machine ignores

`Code.step_loadNcAnyU`: a weak `ld.global.nc` of one register that the facts do not name; any
payload continues to the same state (bytes that do not rebuild fault the thread). -/

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A scalar `.nc` load into a register the facts do not name, continuing to `d'`. -/
theorem step_loadNcAnyU {d d' : C.D} {a : MemAccess} {r base w : Nat} {sp : Space}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r])
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : C.sub d' = 0) (ha' : C.acc d' = [])
    (hn : ∀ x bs, C.next d ⟨C.pc d, .nc x bs⟩ = some (some d')) (hi : C.inv d')
    (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    (seg : SegU K A L g (C.pc d + 1) (C.facts d) (C.pc d') (C.facts d')) : C.StepAtU d where
  site := fun _ => ⟨_, hc, hl, trivial⟩
  step := by
    intro t e u ins hat _ hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
    rw [hr]
    have ht := at_of_atD hat hs ha
    cases hv : rebuild 3 bs with
    | error e =>
      obtain ⟨s, h1, h2⟩ := goodU_of_dead d'
        (Machine.dead_of_fault (K := K) (A := A) (L := L) (g := g) (f := e)
          (u := afterLoad t [r] bs)
          (by simp only [afterLoad, hv]))
      exact .inl (.inr ⟨d', s, hn x bs, h1, h2⟩)
    | ok v =>
      rw [afterLoad_ok ht.2.1 ht.2.2.1 hv]
      obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
      obtain ⟨s, hl', hs''⟩ := landsU (C := C) (d := d') (F := C.facts d)
        (u := { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] })
        ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, hFl, holds_update hR hoff⟩ seg hi hs' ha'
      exact .inl (.inr ⟨d', s, hn x bs, hl', hs''⟩)

end PTX.Flow.Code

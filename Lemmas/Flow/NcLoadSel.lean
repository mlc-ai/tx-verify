-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NcLoadS

@[expose] public section

/-! # A scalar `.nc` word load whose successor follows the word read

`Code.step_loadNcSel` is `Code.step_loadNc` with a successor `nv y` that may also stop following
(`some none`) on a 32-bit word `y` (a word the machine's condition excludes). -/

namespace PTX.Flow
open PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

namespace Code

variable {K : Kernel} {C : Code K A L g}

theorem step_loadNcSel {d : C.D} {nv : BitVec 64 → Option (Option C.D)} {a : MemAccess}
    {r base w : Nat} {sp : Space}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r])
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hok : ∀ x bs y, rebuild 3 bs = .ok (.bits 32 y) → C.next d ⟨C.pc d, .nc x bs⟩ = nv y)
    (hoth : ∀ x bs v, rebuild 3 bs = .ok v → (∀ y, v ≠ .bits 32 y) →
      C.next d ⟨C.pc d, .nc x bs⟩ = some none)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .nc x bs⟩ = none ∨ C.next d ⟨C.pc d, .nc x bs⟩ = some none)
    (hnn : ∀ y, nv y ≠ none) (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    (hland : ∀ y d', nv y = some (some d') →
      C.Lands d (C.pc d + 1) ((r, .bits 32 y) :: C.facts d) d') :
    C.StepOk d := by
  constructor
  intro t e u ins hat hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  rw [hr]
  have ht := at_of_atD hat hs ha
  cases hv : rebuild 3 bs with
  | error e =>
    rcases herr x bs e hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := e) (by simp only [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    rw [afterLoad_ok ht.2.1 ht.2.2.1 hv]
    by_cases h32 : ∃ y, v = .bits 32 y
    · obtain ⟨y, rfl⟩ := h32
      have hst : { setReg t r (.bits 32 y) with pc := t.pc + 1, sub := 0, acc := [] } =
          PTX.next (setReg t r (.bits 32 y)) := by
        have hs0 := ht.2.1
        have ha0 := ht.2.2.1
        cases t
        simp_all [PTX.next, setReg]
      rw [hst]
      have hn := hok x bs y hv
      rcases hnv : nv y with _ | _ | d'
      · exact absurd hnv (hnn y)
      · exact .inl (.inl (hn.trans hnv))
      · exact (hland y d' hnv).cont hi (hn.trans hnv) (At.set ht hoff)
    · exact .inl (.inl (hoth x bs v hv fun y hy => h32 ⟨y, hy⟩))

end Code
end PTX.Flow

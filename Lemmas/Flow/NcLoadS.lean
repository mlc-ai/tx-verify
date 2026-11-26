-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NcLoadU

@[expose] public section

/-! # A scalar `.nc` word load in an exact control machine

`Code.step_loadNc` is `Code.step_loadNcU` for the exact obligation `StepAt`: a 32-bit word
continues to `f x` by an exact segment, another value is a pending stop (`some none`), and bytes
that do not rebuild fault (`none`, the thread is dead). -/

namespace PTX.Flow
open PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

namespace Code

variable {K : Kernel} {C : Code K A L g}

/-- A scalar `.nc` word load into a register the facts do not name. -/
theorem step_loadNc {d : C.D} {f : BitVec 64 → C.D} {a : MemAccess} {r base w : Nat}
    {sp : Space}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r])
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hn : ∀ x bs, C.next d ⟨C.pc d, .nc x bs⟩ = ncNext f bs)
    (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    (hok : ∀ x, C.Lands d (C.pc d + 1) ((r, .bits 32 x) :: C.facts d) (f x)) :
    C.StepAt d where
  site := fun _ => ⟨_, hc, hl, trivial⟩
  step := by
    intro t e u ins hat hi hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
    rw [hr]
    have hnx := hn x bs
    have ht := at_of_atD hat hs ha
    cases hv : rebuild 3 bs with
    | error e =>
      exact .inr ⟨by rw [hnx]; simp only [ncNext, hv],
        Machine.dead_of_fault (f := e) (by simp only [afterLoad, hv])⟩
    | ok v =>
      rw [afterLoad_ok ht.2.1 ht.2.2.1 hv]
      cases v with
      | bits n y =>
        by_cases h32 : n = 32
        · subst h32
          have hst : { setReg t r (.bits 32 y) with pc := t.pc + 1, sub := 0, acc := [] } =
              PTX.next (setReg t r (.bits 32 y)) := by
            have hs0 := ht.2.1
            have ha0 := ht.2.2.1
            cases t
            simp_all [PTX.next, setReg]
          rw [hst]
          exact (hok y).cont hi (by rw [hnx]; simp only [ncNext, hv]) (At.set ht hoff)
        · exact .inl (.inl (by rw [hnx]; simp only [ncNext, hv]; split <;> simp_all))
      | _ => exact .inl (.inl (by rw [hnx]; simp only [ncNext, hv]))

end Code
end PTX.Flow

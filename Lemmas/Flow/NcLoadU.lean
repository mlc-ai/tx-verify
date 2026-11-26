-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section

/-! # A scalar `.nc` load in a UB-tolerant control machine

A weak `ld.global.nc` of one register, located directly, fires a non-coherent read (`.nc`) and
leaves the thread in `afterLoad`. `Code.step_loadNcU` steps a control machine over it: a 32-bit
word continues (the facts gain the word in the destination), another value is a pending stop
(`some none`), and bytes that do not rebuild fault (`none`, the thread is dead). -/

namespace PTX.Flow
open PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- A weak scalar load located directly with `.nc` reads non-coherently into `afterLoad`. -/
theorem fires_loadNc {t u : TState} {a : MemAccess} {pc base w : Nat} {sp : Space} {e : Event}
    (hr : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hs : a.sem = .weak)
    (hnc : a.nc = true) (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ x bs, e = ⟨pc, .nc x bs⟩ ∧ u = afterLoad t a.regs bs := by
  simp only [eventTmpl] at hf
  rw [memTmpl_direct_weakLoad hr hloc hb hk hs, hnc] at hf
  unfold loadTmpl at hf
  simp only [↓reduceIte] at hf
  split at hf
  · exact absurd hf.2 (by simp)
  · split at hf
    · obtain ⟨bs, -, rfl, hu⟩ := hf
      exact ⟨_, bs, rfl, Option.some.inj hu⟩
    · exact absurd hf.2 (by simp)

namespace Code

variable {K : Kernel} {C : Code K A L g}

/-- The successor of a word load: a 32-bit word goes on to `f`, another value stops, bytes that
do not rebuild fault. -/
noncomputable def ncNext {D : Type} (f : BitVec 64 → D) (bs : List (Option Byte)) :
    Option (Option D) :=
  match rebuild 3 bs with
  | .ok (.bits 32 x) => some (some (f x))
  | .ok _ => some none
  | .error _ => none

/-- A scalar `.nc` word load into a register the facts do not name. -/
theorem step_loadNcU {d : C.D} {f : BitVec 64 → C.D} {a : MemAccess} {r base w : Nat}
    {sp : Space}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r])
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hn : ∀ x bs, C.next d ⟨C.pc d, .nc x bs⟩ = ncNext f bs)
    (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    (hok : ∀ x, C.sub (f x) = 0 ∧ C.acc (f x) = [] ∧ C.inv (f x) ∧
      SegU K A L g (C.pc d + 1) ((r, .bits 32 x) :: C.facts d) (C.pc (f x)) (C.facts (f x))) :
    C.StepAtU d where
  site := fun _ => ⟨_, hc, hl, trivial⟩
  step := by
    intro t e u ins hat _ hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
    rw [hn, hr]
    have ht := at_of_atD hat hs ha
    unfold ncNext
    cases hv : rebuild 3 bs with
    | error e =>
      exact .inr ⟨rfl, Machine.dead_of_fault (f := e) (by simp only [afterLoad, hv])⟩
    | ok v =>
      rw [afterLoad_ok ht.2.1 ht.2.2.1 hv]
      cases v with
      | bits n y =>
        by_cases h32 : n = 32
        · subst h32
          obtain ⟨hs', ha', hi, seg⟩ := hok y
          obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
          obtain ⟨s, hl', hs''⟩ := landsU (C := C) (d := f y)
            (F := (r, .bits 32 y) :: C.facts d)
            (u := { setReg t r (.bits 32 y) with pc := t.pc + 1, sub := 0, acc := [] })
            ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, hFl, Function.update_self ..,
              holds_update hR hoff⟩
            seg hi hs' ha'
          exact .inl (.inr ⟨f y, s, rfl, hl', hs''⟩)
        · exact .inl (.inl (by split <;> simp_all))
      | _ => exact .inl (.inl (by split <;> simp_all))

end Code
end PTX.Flow

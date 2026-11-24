-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.Alloc

@[expose] public section

/-! # Step combinators of `tcgen05.alloc`

A proof tool (promoted from the tml-fa4 MMA warp's proof). `tcgen05.alloc` has two events on
lane 0: the allocation, after which the thread stays at the instruction with sub-step 1
(`step_alloc`), and the store of the allocated address, after which it continues at the next
instruction (`step_allocWr`); the other lanes continue after the allocation. Whatever the state,
its template is undefined behaviour, the request or the address store (`allocT`, from the
tml-fa4 MMA warp's proof). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- The templates of a `tcgen05.alloc`: undefined behaviour, the request, or the address store. -/
def AllocT : Tmpl → Prop
  | .ub _ | .tc (.resource ..) _ | .tcAllocStore .. => True
  | _ => False

/-- **The template of a `tcgen05.alloc` is one of `AllocT`**, from any state. -/
theorem allocT {t : TState} {grp : CtaGroup} {b : Nat} {off : Int} {nc : Opnd} :
    AllocT (eventTmpl A L g t (.tcAlloc grp b off nc)) := by
  simp only [eventTmpl, tcTmpl]
  unfold ofExec
  split
  · rename_i m heq
    revert heq
    cases effAddr L g t .shared b off <;> cases readBits L g t 32 nc <;>
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;>
      split_ifs <;> simp only [Except.ok.injEq, IsEmpty.forall_iff] <;> rintro rfl <;> trivial
  · trivial

namespace Code

variable {K : Kernel} {C : Code K A L g}

/-- `tcgen05.alloc` at sub-step 0: lane 0 stays at the instruction with sub-step 1, to the state
`dw` with the same facts; the other lanes continue at the next instruction to `dn`. -/
theorem step_alloc {d dw dn : C.D} {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd}
    {gd : Option (Nat × Bool)}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .tcAlloc group base off nc⟩)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hw : laneOf L g = 0 → ∀ e, C.next d e = some (some dw))
    (hn : laneOf L g ≠ 0 → ∀ e, C.next d e = some (some dn))
    (hwpc : C.pc dw = C.pc d) (hwsub : C.sub dw = 1) (hwacc : C.acc dw = [])
    (hwf : C.facts dw = C.facts d) (hwinv : C.inv d → C.inv dw)
    (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨dst, n, rfl, rfl⟩ := fires_tcAlloc (h.2.1.trans hs) hf
  by_cases hl0 : laneOf L g = 0
  · simp only [hl0, ↓reduceIte]
    refine .inl (.inr ⟨dw, { t with sub := 1 }, hw hl0 _, .refl, ⟨?_, hwinv hi⟩⟩)
    exact ⟨h.1.trans hwpc.symm, hwsub.symm, h.2.2.1.trans (ha.trans hwacc.symm), h.2.2.2.1,
      hwf ▸ h.2.2.2.2⟩
  · simp only [hl0, ↓reduceIte]
    exact hl.cont hi (hn hl0 _) (At.next (at_of_atD h hs ha))

/-- The address store of `tcgen05.alloc` on lane 0 (sub-step 1): the thread continues at the
next instruction. -/
theorem step_allocWr {d dn : C.D} {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd}
    {gd : Option (Nat × Bool)}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .tcAlloc group base off nc⟩)
    (hs : C.sub d = 1) (ha : C.acc d = []) (hn : ∀ e, C.next d e = some (some dn))
    (hl : C.Lands d (C.pc d + 1) (C.facts d) dn) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨a, bs, rfl, rfl⟩ := fires_tcAlloc_write (h.2.1.trans hs) hf
  refine hl.cont hi (hn _) ⟨by simp [h.1], rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩

end Code

end
end PTX.Flow

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ
public import Lemmas.Flow.ElectU

@[expose] public section

/-! # An election under the tag invariant

`Code.electQ`: the strict counterpart of `Code.electU`. The leader goes into the register `r`
(a 32-bit word), the predicate into `p`; the successor follows the leader and the segment after
the election is strict. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem electQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d : C.D} {dst : Nat → C.D}
    {ty : Option DType} {r p : Nat} {mask : Opnd}
    (hc : K.code[C.pc d]? = some ⟨none, .warp ⟨.elect, ty, [some r, some p], [], some mask⟩⟩)
    (hr : r ∉ (C.facts d).map Prod.fst) (hp : p ∉ (C.facts d).map Prod.fst) (hrp : r ≠ p)
    (hn : ∀ mk inst ld, C.next d ⟨C.pc d, .elect mk inst ld⟩ = some (some (dst ld)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ ld, C.sub (dst ld) = 0)
    (ha' : ∀ ld, C.acc (dst ld) = []) (hi : ∀ ld, C.inv (dst ld))
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r, .bits 32), (p, .pred)] ex = true)
    (seg : ∀ ld, SegQ K A L g (QT qt) (C.pc d + 1) ((p, .pred (laneOf L g == ld)) ::
      (r, .bits 32 (BitVec.ofNat 64 ld)) :: C.facts d) (C.pc (dst ld)) (C.facts (dst ld)))
    (e : Event) : C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hc' hQ _ hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  have h0 := at_of_atD h hs ha
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  have hA1 : At (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) (C.pc d)
      ((r, .bits 32 (BitVec.ofNat 64 ld)) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self ..,
      holds_update h0.2.2.2.2 (fun q hq he => hr (he ▸ List.mem_map_of_mem hq))⟩
  have hA2 := At.set (r := p) (v := .pred (laneOf L g == ld)) hA1 (fun q hq he => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hrp he
    · exact hp (he ▸ List.mem_map_of_mem hq))
  have hQ' : QT qt (PTX.next (setReg (setReg t r (.bits 32 (BitVec.ofNat 64 ld))) p
      (.pred (laneOf L g == ld)))) := by
    refine QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' tg hl => ?_)
      (fun r' hl => ?_) hq
    · by_cases h3 : r' = p
      · subst h3
        have e0 : (r' == r) = false := beq_eq_false_iff_ne.mpr (Ne.symm hrp)
        simp [List.lookup, e0] at hl
        subst hl
        exact ⟨laneOf L g == ld, by simp [PTX.next, setReg]⟩
      · by_cases h0 : r' = r
        · subst h0
          simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
          subst hl
          exact ⟨BitVec.ofNat 64 ld, by simp [PTX.next, setReg, Function.update_of_ne h3]⟩
        · have e1 : (r' == r) = false := by simpa using h0
          have e2 : (r' == p) = false := by simpa using h3
          simp [List.lookup, e1, e2] at hl
    · obtain ⟨h0, h3⟩ := lookup2_none hl
      simp [PTX.next, setReg, Function.update_of_ne h0, Function.update_of_ne h3]
  obtain ⟨t', hr', hg, hq'⟩ := landQ hA2 hQ' (seg ld) (hi ld) (hs' ld) (ha' ld)
  exact .inl ⟨dst ld, t', hn mk inst ld, hr', hg, hq'⟩

end PTX.Flow.Code

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.DataLoad

@[expose] public section

/-! # A vector load whose loaded words become facts

`Code.ldvDU` is `Code.ldvU` (`Lemmas/Flow/CtlStepsU.lean`) for a machine that names the loaded
words in the facts after the last element: the segment after it starts from a table
`factsFrom live' (val' v)` over the registers live after the load, whose values are the loaded
words on the load's registers (`holds_setRegs_zip`) and the state's before on the others. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.EventFrame

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An element of a vector load into registers the facts do not name before it; the last element
adds the loaded words to the facts the segment after it starts from. -/
theorem ldvDU {d : C.D} {dok : Value → C.D} {dbad : C.D} {a : MemAccess} {live : List Nat}
    {val : Nat → Value}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dok v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = some (some dbad))
    (mid : C.sub d + 1 < a.regs.length → ∀ v, C.pc (dok v) = C.pc d ∧
      C.sub (dok v) = C.sub d + 1 ∧ C.acc (dok v) = C.acc d ++ [v] ∧
      C.facts (dok v) = C.facts d ∧ C.inv (dok v))
    (hF : C.facts d = factsFrom live val)
    (hnd : a.regs.Nodup) {live' : List Nat} {val' : Value → Nat → Value}
    (hlive : ∀ r ∈ live', r ∈ a.regs ∨ r ∈ live)
    (hold : ∀ v, ∀ r ∈ live', r ∉ a.regs → val' v r = val r)
    (hnew : ∀ v, ∀ r ∈ live', r ∈ a.regs → (r, val' v r) ∈ a.regs.zip (C.acc d ++ [v]))
    (last : ¬ C.sub d + 1 < a.regs.length → ∀ v, C.sub (dok v) = 0 ∧ C.acc (dok v) = [] ∧
      C.inv (dok v) ∧ SegU K A L g (C.pc d + 1) (factsFrom live' (val' v))
        (C.pc (dok v)) (C.facts (dok v))) :
    C.StepAtU d where
  site := fun _ => ⟨_, hc0, hl, trivial⟩
  step := by
    intro t e u ins h hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans hc0)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
    obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
    cases hv : rebuild 3 bs with
    | error f =>
      obtain ⟨s, hs1, hs2⟩ := goodU_of_dead dbad
        (Machine.dead_of_fault (K := K) (A := A) (L := L) (g := g) (f := f)
          (u := afterLoad t a.regs bs)
          (by simp [afterLoad, hv]))
      exact .inl (.inr ⟨dbad, s, herr x bs f hv, hs1, hs2⟩)
    | ok v =>
      by_cases hm : C.sub d + 1 < a.regs.length
      · obtain ⟨hpc, hs, ha, hF', hinv⟩ := mid hm v
        have hm' : t.sub + 1 < a.regs.length := by rw [hS0]; exact hm
        have hu : afterLoad t a.regs bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
          simp [afterLoad, hv, hm']
        rw [hu]
        refine .inl (.inr ⟨dok v, _, hok x bs v hv, .refl,
          .inl ⟨⟨?_, ?_, ?_, hFl, ?_⟩, hinv⟩⟩)
        · exact hP.trans hpc.symm
        · show t.sub + 1 = C.sub (dok v)
          rw [hS0, hs]
        · show t.acc ++ [v] = C.acc (dok v)
          rw [hA, ha]
        · rw [hF']; exact hR
      · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm v
        have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hS0]; exact hm
        have hu : afterLoad t a.regs bs =
            { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
          simp [afterLoad, hv, hm']
        rw [hu]
        obtain ⟨-, -, -, hskF⟩ := setRegs_skel t a.regs (t.acc ++ [v])
        have hreg := hR
        rw [hF] at hreg
        have hz := holds_setRegs_zip t a.regs (t.acc ++ [v]) hnd
        obtain ⟨s, hl', hs'⟩ := landsU
          (u := { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] })
          ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl,
            by show (setRegs t a.regs (t.acc ++ [v])).fault = none; rw [hskF]; exact hFl,
            by
              refine holds_of_mem fun r w hm => ?_
              obtain ⟨r', hr', hw⟩ := List.mem_map.mp hm
              simp only [Prod.mk.injEq] at hw
              obtain ⟨rfl, rfl⟩ := hw
              have hz' : Holds (setRegs t a.regs (t.acc ++ [v])).regs
                  (a.regs.zip (C.acc d ++ [v])) := by rw [← hA]; exact hz
              by_cases hin : r' ∈ a.regs
              · exact holds_mem hz' (hnew v r' hr' hin)
              · have hl : r' ∈ live := (hlive r' hr').resolve_left hin
                rw [hold v r' hr' hin]
                show (setRegs t a.regs (t.acc ++ [v])).regs r' = _
                rw [setRegs_other _ _ _ _ hin]
                exact holds_mem hreg (mem_factsFrom hl)⟩
          seg hinv hs0 ha0
        exact .inl (.inr ⟨dok v, s, hok x bs v hv, hl', hs'⟩)

end PTX.Flow.Code

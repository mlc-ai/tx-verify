-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.DataLoad
public import Lemmas.Flow.StrictWindow

@[expose] public section

/-! # An element of a vector load, strict for one event

`Code.ldvFor` is `Code.ldvU` (`Lemmas/Flow/CtlStepsU.lean`) as a strict step (`Code.StepFor`) for
one event: the bytes the event reads rebuild a value (`hrb`), so the thread does not fault at the
load, and the segment after the last element is strict (`Seg`, not `SegU`), so the state it
reaches is strictly good. The words loaded are the facts the segment starts from
(`factsFrom live' (val' v)`, `holds_setRegs_zip`), as in `Code.ldvDU`. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.EventFrame

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An element of a vector load, strict for the event `e`, whose bytes rebuild a value. -/
theorem ldvFor {d : C.D} {dok : Value → C.D} {a : MemAccess} {live : List Nat}
    {val : Nat → Value} {e : Event}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same)
    (hrb : ∀ x bs, e = ⟨C.pc d, .rd x bs⟩ → ∃ v, rebuild 3 bs = .ok v)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .rd x bs⟩ = some (some (dok v)))
    (mid : C.sub d + 1 < a.regs.length → ∀ v, C.pc (dok v) = C.pc d ∧
      C.sub (dok v) = C.sub d + 1 ∧ C.acc (dok v) = C.acc d ++ [v] ∧
      C.facts (dok v) = C.facts d ∧ C.inv (dok v))
    (hF : C.facts d = factsFrom live val)
    (hnd : a.regs.Nodup) {live' : List Nat} {val' : Value → Nat → Value}
    (hlive : ∀ r ∈ live', r ∈ a.regs ∨ r ∈ live)
    (hold : ∀ v, ∀ r ∈ live', r ∉ a.regs → val' v r = val r)
    (hnew : ∀ v, ∀ r ∈ live', r ∈ a.regs → (r, val' v r) ∈ a.regs.zip (C.acc d ++ [v]))
    (last : ¬ C.sub d + 1 < a.regs.length → ∀ v, C.sub (dok v) = 0 ∧ C.acc (dok v) = [] ∧
      C.inv (dok v) ∧ ∃ n, Seg K A L g n (C.pc d + 1) (factsFrom live' (val' v))
        (C.pc (dok v)) (C.facts (dok v))) :
    C.StepFor d e := by
  intro t u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
  obtain ⟨v, hv⟩ := hrb x bs rfl
  by_cases hm : C.sub d + 1 < a.regs.length
  · obtain ⟨hpc, hs, ha, hF', hinv⟩ := mid hm v
    have hm' : t.sub + 1 < a.regs.length := by rw [hS0]; exact hm
    have hu : afterLoad t a.regs bs = { t with sub := t.sub + 1, acc := t.acc ++ [v] } := by
      simp [afterLoad, hv, hm']
    rw [hu]
    refine .inl (.inr ⟨dok v, _, hok x bs v hv, .refl, ⟨?_, ?_, ?_, hFl, ?_⟩, hinv⟩)
    · exact hP.trans hpc.symm
    · show t.sub + 1 = C.sub (dok v)
      rw [hS0, hs]
    · show t.acc ++ [v] = C.acc (dok v)
      rw [hA, ha]
    · rw [hF']; exact hR
  · obtain ⟨hs0, ha0, hinv, n, seg⟩ := last hm v
    have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hS0]; exact hm
    have hu : afterLoad t a.regs bs =
        { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      simp [afterLoad, hv, hm']
    rw [hu]
    obtain ⟨-, -, -, hskF⟩ := setRegs_skel t a.regs (t.acc ++ [v])
    have hreg := hR
    rw [hF] at hreg
    have hz := holds_setRegs_zip t a.regs (t.acc ++ [v]) hnd
    have hat : At { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }
        (C.pc d + 1) (factsFrom live' (val' v)) := by
      refine ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl,
        by show (setRegs t a.regs (t.acc ++ [v])).fault = none; rw [hskF]; exact hFl, ?_⟩
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
        exact holds_mem hreg (mem_factsFrom hl)
    obtain ⟨t', hr, ht⟩ := seg _ hat
    exact .inl (.inr ⟨dok v, t', hok x bs v hv, run_rtg hr,
      ⟨ht.1, ht.2.1.trans hs0.symm, ht.2.2.1.trans ha0.symm, ht.2.2.2.1, ht.2.2.2.2⟩, hinv⟩)

end PTX.Flow.Code

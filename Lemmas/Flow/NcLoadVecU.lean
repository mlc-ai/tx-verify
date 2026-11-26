-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NcLoadU
public import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # An element of a vector `.nc` load in a UB-tolerant control machine

`Code.ldvNcU` is `Code.ldvU` for a weak, directly located `ld.global.nc` of several registers
(`fires_loadNc`): before the last element the machine accumulates the value at the same
instruction; at the last it continues by a segment, the destinations not named by the facts.
Bytes that do not rebuild fault (the machine goes on to `dbad`). -/

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An element of a vector `.nc` load into registers the facts do not name. -/
theorem ldvNcU {d : C.D} {dok : Value → C.D} {dbad : C.D} {a : MemAccess} {live : List Nat}
    {val : Nat → Value} {base w : Nat} {sp : Space}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .nc x bs⟩ = some (some (dok v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .nc x bs⟩ = some (some dbad))
    (mid : C.sub d + 1 < a.regs.length → ∀ v, C.pc (dok v) = C.pc d ∧
      C.sub (dok v) = C.sub d + 1 ∧ C.acc (dok v) = C.acc d ++ [v] ∧
      C.facts (dok v) = C.facts d ∧ C.inv (dok v))
    (hF : C.facts d = factsFrom live val) (hoff : ∀ r ∈ live, r ∉ a.regs)
    (last : ¬ C.sub d + 1 < a.regs.length → ∀ v, C.sub (dok v) = 0 ∧ C.acc (dok v) = [] ∧
      C.inv (dok v) ∧ SegU K A L g (C.pc d + 1) (C.facts d) (C.pc (dok v)) (C.facts (dok v))) :
    C.StepAtU d where
  site := fun _ => ⟨_, hc0, hl, trivial⟩
  step := by
    intro t e u ins h hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans hc0)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
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
        obtain ⟨s, hl', hs'⟩ := landsU
          (u := { setRegs t a.regs (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] })
          ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl,
            by show (setRegs t a.regs (t.acc ++ [v])).fault = none; rw [hskF]; exact hFl,
            by rw [hF]; exact holds_setRegs_frame hreg (fun r hr => ⟨hoff r hr, hr, rfl⟩)⟩
          seg hinv hs0 ha0
        exact .inl (.inr ⟨dok v, s, hok x bs v hv, hl', hs'⟩)

end PTX.Flow.Code

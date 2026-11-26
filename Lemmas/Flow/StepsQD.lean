-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # Strict vector `.nc` load whose words become facts

`Code.ldvNcDQ` is `Code.ldvNcQ` (`Lemmas/Flow/StepsQ.lean`) for a machine that names the loaded
words in the facts after the last element (the first element's word is `y0`, the machine's
accumulator `[.bits 32 y0]`): the segment after the last element starts from
`factsFrom live' (val' y)`. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An element of a pair of `.nc` loads into registers `r0 r1` the facts do not name; the payload
is a 32-bit word (`hW`). -/
theorem ldvNcDQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d : C.D}
    {dok : BitVec 64 → C.D} {a : MemAccess} {y0 : BitVec 64}
    {live : List Nat} {val : Nat → Value} {base w r0 r1 : Nat} {sp : Space}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩) (_hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hregs : a.regs = [r0, r1]) (hr01 : r0 ≠ r1)
    (hW : ∀ e, Wf e → ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y))
    (hlast : ¬ C.sub d + 1 < 2 → C.acc d = [.bits 32 y0])
    (hok : ∀ x bs y, rebuild 3 bs = .ok (.bits 32 y) →
      C.next d ⟨C.pc d, .nc x bs⟩ = some (some (dok y)))
    (mid : C.sub d + 1 < 2 → ∀ y, C.pc (dok y) = C.pc d ∧
      C.sub (dok y) = C.sub d + 1 ∧ C.acc (dok y) = C.acc d ++ [.bits 32 y] ∧
      C.facts (dok y) = C.facts d ∧ C.inv (dok y))
    (hF : C.facts d = factsFrom live val) (hoff : ∀ r ∈ live, r ∉ a.regs)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r0, .bits 32), (r1, .bits 32)] ex = true)
    (last : ¬ C.sub d + 1 < 2 → ∀ y, C.sub (dok y) = 0 ∧ C.acc (dok y) = [] ∧
      C.inv (dok y) ∧ SegQ K A L g (QT qt) (C.pc d + 1)
        ((r0, .bits 32 y0) :: (r1, .bits 32 y) :: C.facts d) (C.pc (dok y))
        (C.facts (dok y))) (e : Event) : C.StepForQ (QT qt) Wf d e := by
  intro t u ins h hi hc hQ hWe hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
  obtain ⟨y, hy⟩ := hW _ hWe x bs rfl
  have hlen : a.regs.length = 2 := by rw [hregs]; rfl
  by_cases hm : C.sub d + 1 < 2
  · obtain ⟨hpc, hs, ha, hF', hinv⟩ := mid hm y
    have hm' : t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
    have hu : afterLoad t a.regs bs =
        { t with sub := t.sub + 1, acc := t.acc ++ [.bits 32 y] } := by
      simp [afterLoad, hy, hm']
    rw [hu]
    refine .inl ⟨dok y, _, hok x bs y hy, .refl, ⟨⟨?_, ?_, ?_, hFl, ?_⟩, hinv⟩,
      QT.same hQ rfl rfl⟩
    · exact hP.trans hpc.symm
    · show t.sub + 1 = C.sub (dok _)
      rw [hS0, hs]
    · show t.acc ++ [_] = C.acc (dok _)
      rw [hA, ha]
    · rw [hF']; exact hR
  · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm y
    have h0 := hlast hm
    have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
    have hacc : t.acc = [.bits 32 y0] := hA.trans h0
    obtain ⟨u0, hu0⟩ : ∃ u0, u0 = afterLoad t a.regs bs := ⟨_, rfl⟩
    have hu : u0 = { setRegs t [r0, r1] [.bits 32 y0, .bits 32 y] with
        pc := t.pc + 1, sub := 0, acc := [] } := by
      have hm2 : ¬ t.sub = 0 := by omega
      rw [hu0]; simp [afterLoad, hy, hm2, hacc, hregs]
    obtain ⟨-, -, -, hskF⟩ := setRegs_skel t [r0, r1] [.bits 32 y0, .bits 32 y]
    have hAt : At u0 (C.pc d + 1) ((r0, .bits 32 y0) :: (r1, .bits 32 y) :: C.facts d) := by
      have hreg := hR
      rw [hF] at hreg
      rw [hu]
      refine ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, ?_, ?_⟩
      · show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).fault = none
        rw [hskF]; exact hFl
      · have hoff' : ∀ r ∈ live, r ∉ [r0, r1] := by rw [← hregs]; exact hoff
        refine ⟨?_, ?_, ?_⟩
        · show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).regs r0 = _
          simp [setRegs, setReg, Function.update_of_ne hr01]
        · show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).regs r1 = _
          simp [setRegs, setReg]
        · rw [hF]
          exact holds_setRegs_frame hreg (fun r hr => ⟨hoff' r hr, hr, rfl⟩)
    have hQ' : QT qt u0 := by
      rw [hu]
      refine QT.after hQ hexT hP (by simp [hP]) (fun r tg hl => ?_) (fun r hl => ?_) hq
      · by_cases h1 : r = r1
        · subst h1
          by_cases e0 : (r == r0) = true <;> simp [List.lookup, e0] at hl <;> subst hl <;>
            exact ⟨y, by simp [setRegs, setReg]⟩
        · by_cases h0 : r = r0
          · subst h0
            simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
            subst hl
            exact ⟨y0, by simp [setRegs, setReg, Function.update_of_ne h1]⟩
          · have e1 : (r == r0) = false := by simpa using h0
            have e2 : (r == r1) = false := by simpa using h1
            simp [List.lookup, e1, e2] at hl
      · obtain ⟨h0, h1⟩ := lookup2_none hl
        simp [setRegs, setReg, Function.update_of_ne h1, Function.update_of_ne h0]
    obtain ⟨t', hr, hg, hq'⟩ := landQ hAt hQ' seg hinv hs0 ha0
    rw [← hu0]
    exact .inl ⟨dok y, t', hok x bs y hy, hr, hg, hq'⟩

end PTX.Flow.Code

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NcLoadVecU
public import Lemmas.Flow.DataLoad

@[expose] public section

/-! # A vector `.nc` load whose words become facts

`Code.ldvNcDU` is `Code.ldvNcU` (`Lemmas/Flow/NcLoadVecU.lean`) for a machine that names the
loaded words in the facts after the last element, as `Code.ldvDU` does for an ordinary load: only
a 32-bit payload continues (`dok`), another value ends the machine, bytes that do not rebuild
fault. The segment after the last element starts from `factsFrom live' (val' y)`, whose values
are the loaded words on the load's registers and the state's before on the others. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.EventFrame

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An element of a vector `.nc` load into registers the facts do not name before it. -/
theorem ldvNcDU {d : C.D} {dok : BitVec 64 → C.D} {a : MemAccess} {live : List Nat}
    {val : Nat → Value} {base w : Nat} {sp : Space}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hregs : a.regs = [r0, r1]) (hr01 : r0 ≠ r1)
    (hlast : ¬ C.sub d + 1 < 2 → C.acc d = [.bits 32 y0])
    (hok : ∀ x bs y, rebuild 3 bs = .ok (.bits 32 y) →
      C.next d ⟨C.pc d, .nc x bs⟩ = some (some (dok y)))
    (hoth : ∀ x bs v, rebuild 3 bs = .ok v → (∀ y, v ≠ .bits 32 y) →
      C.next d ⟨C.pc d, .nc x bs⟩ = some none)
    (herr : ∀ x bs f, rebuild 3 bs = .error f → C.next d ⟨C.pc d, .nc x bs⟩ = none)
    (mid : C.sub d + 1 < 2 → ∀ y, C.pc (dok y) = C.pc d ∧
      C.sub (dok y) = C.sub d + 1 ∧ C.acc (dok y) = C.acc d ++ [.bits 32 y] ∧
      C.facts (dok y) = C.facts d ∧ C.inv (dok y))
    (hF : C.facts d = factsFrom live val) (hoff : ∀ r ∈ live, r ∉ a.regs)
    (last : ¬ C.sub d + 1 < 2 → ∀ y, C.sub (dok y) = 0 ∧ C.acc (dok y) = [] ∧
      C.inv (dok y) ∧ SegU K A L g (C.pc d + 1)
        ((r0, .bits 32 y0) :: (r1, .bits 32 y) :: C.facts d) (C.pc (dok y)) (C.facts (dok y))) :
    C.StepAtU d where
  site := fun _ => ⟨_, hc0, hl, trivial⟩
  step := by
    intro t e u ins h hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans hc0)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
    obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
    cases hv : rebuild 3 bs with
    | error f =>
      exact .inr ⟨herr x bs f hv,
        Machine.dead_of_fault (K := K) (A := A) (L := L) (g := g) (f := f)
          (u := afterLoad t a.regs bs) (by simp [afterLoad, hv])⟩
    | ok v =>
      by_cases hb32 : ∃ y, v = .bits 32 y
      · obtain ⟨y, rfl⟩ := hb32
        have hlen : a.regs.length = 2 := by rw [hregs]; rfl
        by_cases hm : C.sub d + 1 < 2
        · obtain ⟨hpc, hs, ha, hF', hinv⟩ := mid hm y
          have hm' : t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
          have hu : afterLoad t a.regs bs =
              { t with sub := t.sub + 1, acc := t.acc ++ [.bits 32 y] } := by
            simp [afterLoad, hv, hm']
          rw [hu]
          refine .inl (.inr ⟨dok y, _, hok x bs y hv, .refl,
            .inl ⟨⟨?_, ?_, ?_, hFl, ?_⟩, hinv⟩⟩)
          · exact hP.trans hpc.symm
          · show t.sub + 1 = C.sub (dok y)
            rw [hS0, hs]
          · show t.acc ++ [.bits 32 y] = C.acc (dok y)
            rw [hA, ha]
          · rw [hF']; exact hR
        · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm y
          have h0 := hlast hm
          have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
          have hacc : t.acc = [.bits 32 y0] := hA.trans h0
          have hm2 : ¬ t.sub = 0 := by omega
          have hu : afterLoad t a.regs bs =
              { setRegs t [r0, r1] [.bits 32 y0, .bits 32 y] with
                pc := t.pc + 1, sub := 0, acc := [] } := by
            simp [afterLoad, hv, hm2, hacc, hregs]
          rw [hu]
          obtain ⟨-, -, -, hskF⟩ := setRegs_skel t [r0, r1] [.bits 32 y0, .bits 32 y]
          have hreg := hR
          rw [hF] at hreg
          have hoff' : ∀ r ∈ live, r ∉ [r0, r1] := by rw [← hregs]; exact hoff
          obtain ⟨s, hl', hs'⟩ := landsU
            (u := { setRegs t [r0, r1] [.bits 32 y0, .bits 32 y] with
              pc := t.pc + 1, sub := 0, acc := [] })
            ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl,
              by show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).fault = none
                 rw [hskF]; exact hFl,
              by
                refine ⟨?_, ?_, ?_⟩
                · show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).regs r0 = _
                  simp [setRegs, setReg, Function.update_of_ne hr01]
                · show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).regs r1 = _
                  simp [setRegs, setReg]
                · rw [hF]
                  exact holds_setRegs_frame hreg (fun r hr => ⟨hoff' r hr, hr, rfl⟩)⟩
            seg hinv hs0 ha0
          exact .inl (.inr ⟨dok y, s, hok x bs y hv, hl', hs'⟩)
      · exact .inl (.inl (hoth x bs v hv fun y hy => hb32 ⟨y, hy⟩))

end PTX.Flow.Code

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.FloatRules
public import Kernels.InklingRelDecode.Proof.Lib.WinFacts
import Kernels.InklingRelDecode.Proof.Lib.IntStep
import Kernels.InklingRelDecode.Flow.Code.Part040
import Kernels.InklingRelDecode.Flow.Code.Part041
import Lemmas.Flow.FloatOutcome
import Lemmas.Flow.TypedFloatH
import Lemmas.Flow.Step.RuleStep

@[expose] public section

/-! # The steps of the epilogue's log normalizer

`lg2.approx.ftz.f32` at pc 2562 (read as the exact `log2` of a positive operand by `lg2Exact`),
`fma.rn.f32` at pc 2563 (exact), and the `selp.b32` at pc 2680 that picks the `-inf` pattern or the
normalizer. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof PTX.Assumption

private abbrev lg2Op : Op := Op.float
  { op := FOp.lg2, ty := { fmt := FloatFmt.f32 }, mode := FMode.approx, ftz := true,
    dsts := [some 1759], srcs := [Opnd.reg 1915] }

private abbrev fmaOp : Op := Op.float
  { op := FOp.fma, ty := { fmt := FloatFmt.f32 }, rnd := some FloatRound.rn, dsts := [some 524],
    srcs := [Opnd.reg 498, Opnd.reg 1914, Opnd.reg 1759] }

private theorem exec_of_tau {L : Launch} {g : Nat} {b t : TState} {op : Op}
    (hc : kernel.code[b.pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (h : Tau kernel Assumptions.all L g b t) :
    execLocalA Assumptions.all L g b op = .ok t := by
  unfold Tau out at h
  cases hf : b.fault with
  | some f => simp [hf] at h
  | none =>
    simp only [hf, hc, guardHolds, hl, pure, Except.pure, ↓reduceIte] at h
    cases hx : execLocalA Assumptions.all L g b op with
    | error f => simp [hx] at h
    | ok u =>
      simp only [hx, Out.tau.injEq] at h
      rw [h]

theorem lg2_tau {L : Launch} {g : Nat} {c w : TState} {l : ℝ} (hpc : c.pc = 2562) (hl : 0 < l)
    (h : c.regs 1915 = some (.float .f32 l)) (ht : Tau kernel Assumptions.all L g c w) :
    w.pc = 2563 ∧ w.regs 1759 = some (.float .f32 (Real.logb 2 l)) ∧
      ∀ r, r ≠ 1759 → w.regs r = c.regs r := by
  have hc := Flow.code_2562
  rw [← hpc] at hc
  have hx := exec_of_tau (g := g) (L := L) hc rfl ht
  have hem : Assumptions.emuSites.contains c.pc = false := by rw [hpc]; decide
  have hS : Assumption.SegFreePc Assumptions.all c.pc := segFree hem
  have hr : execLocalRule Assumptions.all L g c lg2Op =
      .ok (PTX.next (setReg c 1759 (.float .f32 (Real.logb 2 l)))) := by
    have h4 : Assumptions.lg2Exact.localRule L g c lg2Op =
        some (.ok (PTX.next (setReg c 1759 (.float .f32 (Real.logb 2 l))))) := by
      have hrd : readERealOpnd c .f32 (.reg 1915) = some (.ok (l : EReal)) := by
        simp only [readERealOpnd, readReg, h]
        exact readEReal_of_valFloat valFloat_float
      simp only [Assumptions.lg2Exact, Assumptions.lg2Sites, hpc, hrd, bindRead]
      simp [hl]
      rfl
    rw [show Assumptions.all = _ from rfl]
    refine execLocalRule_cons_none ?_ (execLocalRule_cons_none ?_
      (execLocalRule_cons_none ?_ (execLocalRule_cons_some h4)))
    · exact Assumption.idealReal_localRule_none (fun f hf => by simp [FloatForm.ofOp] at hf)
    · exact Assumption.approxExact_localRule_none (fun f hf => by simp [ApproxForm.ofOp] at hf)
    · rfl
  rw [hS.exec rfl, hr] at hx
  obtain rfl := (Except.ok.inj hx).symm
  refine ⟨by simp [PTX.next, setReg, hpc], by simp [PTX.next, setReg], fun r hr => ?_⟩
  simp [PTX.next, setReg, Function.update_of_ne hr]

theorem fma_tau {L : Launch} {g : Nat} {c w : TState} {sc mr z : ℝ} (hpc : c.pc = 2563)
    (h1 : c.regs 498 = some (.float .f32 sc)) (h2 : c.regs 1914 = some (.float .f32 mr))
    (h3 : c.regs 1759 = some (.float .f32 z)) (ht : Tau kernel Assumptions.all L g c w) :
    w.pc = 2564 ∧ w.regs 524 = some (.float .f32 (sc * mr + z)) ∧
      ∀ r, r ≠ 524 → w.regs r = c.regs r := by
  have hc := Flow.code_2563
  rw [← hpc] at hc
  have hx := exec_of_tau (g := g) (L := L) hc rfl ht
  have hem : Assumptions.emuSites.contains c.pc = false := by rw [hpc]; decide
  have hI : IdealAt Assumptions.all (.fma .f32) L g c := ideal_at (by simp [idealForms]) hem
  have hD : DeclineAt Assumptions.all (.fma .f32) L g c :=
    decline_at (by simp [idealForms]) hem (by omega) (by omega) (by omega)
  have he := PTX.Flow.TyG.exec_fmaE_at (rnd := .rn) (fz := false) (d := 524) (a := .reg 498)
    (b := .reg 1914)
    (c := .reg 1759) hI hD (OpndIs.reg h1) (OpndIs.reg h2) (OpndIs.reg h3)
  rw [floatE_fma_fin valFloat_float valFloat_float valFloat_float] at he
  have hx' : execLocalA Assumptions.all L g c fmaOp = _ := he
  rw [hx'] at hx
  simp only [Except.map] at hx
  obtain rfl := (Except.ok.inj hx).symm
  refine ⟨by simp [PTX.next, setReg, hpc], by simp [PTX.next, setReg], fun r hr => ?_⟩
  simp [PTX.next, setReg, Function.update_of_ne hr]

theorem selp_tau {L : Launch} {g : Nat} {c w : TState} {p : Bool} (hpc : c.pc = 2680)
    (hp : c.regs 178 = some (.pred p)) (hv : p = false → ∃ v, c.regs 524 = some v ∧ v.bytes = 4)
    (ht : Tau kernel Assumptions.all L g c w) :
    w.pc = 2681 ∧ (∀ r, r ≠ 1831 → w.regs r = c.regs r) ∧
      (p = true → w.regs 1831 = some (.bits 32 (truncBits 32 (BitVec.ofInt 64 (-8388608))))) ∧
      (p = false → ∃ v, c.regs 524 = some v ∧ w.regs 1831 = some v) := by
  have hc := Flow.code_2680
  rw [← hpc] at hc
  have hx := exec_of_tau (g := g) (L := L) hc rfl ht
  have hem : Assumptions.emuSites.contains c.pc = false := by rw [hpc]; decide
  rw [(segFree hem).exec rfl, execLocalRule_of_none (fun a ha => Lib.intRules a ha),
    execLocal_selp (i := ⟨.selp, .int .b 32, false, [some 1831],
      [.imm (-8388608), .reg 524, .reg 178]⟩) rfl,
    execMove] at hx
  simp only [DType.width, readReg, hp, bind, Except.bind, pure, Except.pure] at hx
  cases p
  · obtain ⟨v, hv, hb⟩ := hv rfl
    simp only [Bool.false_eq_true, ↓reduceIte, readValue, readReg, hv] at hx
    simp only [pure, Except.pure, show v.bytes = 32 / 8 from hb, ↓reduceIte] at hx
    obtain rfl := (Except.ok.inj hx).symm
    refine ⟨by simp [PTX.next, setReg, hpc], fun r hr => ?_, fun h => absurd h (by simp),
      fun _ => ⟨v, hv, by simp [PTX.next, setReg]⟩⟩
    simp [PTX.next, setReg, Function.update_of_ne hr]
  · simp only [↓reduceIte, readValue, readBits] at hx
    simp only [pure, Except.pure, Value.bytes, bind, Except.bind] at hx
    simp at hx
    subst hx
    refine ⟨by simp [PTX.next, setReg, hpc], fun r hr => ?_, fun _ => by simp [PTX.next, setReg],
      fun h => absurd h (by simp)⟩
    simp [PTX.next, setReg, Function.update_of_ne hr]

end PTX.Kernels.InklingRelDecode.Proof.Lib

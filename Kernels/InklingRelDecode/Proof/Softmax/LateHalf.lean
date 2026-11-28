-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.LateStep
public import Kernels.InklingRelDecode.Proof.Lib.FloatPlain3
public import Lemmas.Flow.TypedHalfG
public import Lemmas.Flow.StepsQFT

@[expose] public section

/-! # The bias pieces of the data lanes, proved once

`HalfStep` (`Lemmas/Flow/TypedHalfG.lean`) at the pcs of the pack, unpack and widening of the bias
path: the registers they read hold halves (`Iface.LateValues.half`), nothing else is needed. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.Iface PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- What the single and the bias pieces use of a state the lane reaches, the reciprocal of the
epilogue (the operand at pc 2602 is not a zero) and the software `exp2` (its input is not
`+inf`). -/
def LateR' (L : Launch) (g : Nat) (t : TState) : Prop :=
  LateR L g t ∧ (halfPc t.pc = true → ∀ i, kernel.code[t.pc]? = some i → ∀ srcs,
    halfSrcs i.op = some srcs → ∀ r, .reg r ∈ srcs → ∃ v, t.regs r = some v ∧ halfSrcOk i.op v) ∧
  (t.pc = 2602 → ∀ x : EReal, readERealOpnd t .f32 (.reg 1762) = some (.ok x) → x ≠ 0) ∧
  (Assumptions.emuSites.contains t.pc = true → t.sub = 0 → t.acc = [] →
    ∀ asg, Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) [] = some asg →
      ∃ x : EReal, readERealOpnd t .f32 (.reg (Assumptions.emuReg asg .x)) = some (.ok x) ∧ x ≠ ⊤)

/-- The pcs a window may take as bias pieces: the data lanes' range, away from the three
single-instruction readings. -/
def halfOk (pc : Nat) : Bool := lateRange pc && pc != 600 && pc != 807 && pc != 2562

theorem halfOuts_srcs {op : Op} {o : EnvF × List Nat} (h : halfOuts op = some o) :
    ∃ srcs, halfSrcs op = some srcs ∧ ∀ r, r ∈ halfRegs op ↔ .reg r ∈ srcs := by
  cases op with
  | move m =>
    rcases m with ⟨kind, ty, dsts, srcs⟩
    unfold halfOuts at h
    simp only at h
    split at h
    · rename_i k d a b
      exact ⟨[.reg a, .reg b], by simp [halfSrcs, DType.width], by simp [halfRegs]⟩
    · rename_i k lo hi a
      exact ⟨[.reg a], by simp [halfSrcs, DType.width], by simp [halfRegs]⟩
    · simp at h
  | cvt c =>
    simp only [halfOuts] at h
    split at h
    · rename_i ss r hss
      split_ifs at h with hm
      simp only [decide_eq_true_eq] at hm
      generalize c.d = d at *
      subst hm
      exact ⟨[.reg r], by simp [halfSrcs], by simp [halfRegs]⟩
    · simp at h
  | _ => simp [halfOuts] at h

/-- **The bias pieces of the data lanes** at the pcs `halfOk` takes. -/
theorem half_late {pc : Nat} {o : EnvF × List Nat} (hk : halfOk pc = true)
    (ho : ∀ op, kernel.code[pc]? = some ⟨none, op⟩ → halfOuts op = some o) :
    HalfStepO kernel Assumptions.all L g (LateR' L g) pc o := by
  simp only [halfOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
  obtain ⟨⟨⟨hr, h6⟩, h8⟩, h25⟩ := hk
  have hp : ∀ pc', pc ≤ pc' → pc' < pc + 1 → PlainPc pc' := fun pc' h1 h2 => by
    obtain rfl : pc' = pc := by omega
    exact ⟨lateRange_emu hr, h25, h6, h8⟩
  have hfp := floatPlain3 (L := L) (g := g) hp
  refine half_step ho hfp.plain.plain.shape hfp.plain.plain.segs hfp.plain.plain.widen ?_
  intro op hc t hpc hR r hmem
  obtain ⟨srcs, hs, hiff⟩ := halfOuts_srcs (ho op hc)
  have hh : halfPc t.pc = true := by
    show (lateRange t.pc && match kernel.code[t.pc]? with
      | some i => (halfSrcs i.op).isSome | none => false) = true
    rw [hpc, hr, hc]
    simp [hs]
  exact hR.2.1 hh _ (by rw [hpc]; exact hc) srcs hs r ((hiff r).mp hmem)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax

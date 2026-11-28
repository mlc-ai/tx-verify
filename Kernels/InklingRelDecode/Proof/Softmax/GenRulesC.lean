-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRules
public import Kernels.InklingRelDecode.Proof.Lib.AlphaAt
public import Lemmas.Flow.FloatOutcome

@[expose] public section

/-! # The readings of the setup constants' three float instructions

`div.full.f32` at pc 600 (`divFullExact`), `mul.f32` at 601 and `neg.f32` at 807 as the outcome
functions of generated runs: the exact value on numbers, Core's outcome where the reading
declines. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- `div.full.f32`. -/
abbrev divFullI : FloatInstr := { divI false with mode := .full }

/-- **The outcome of `div.full.f32`** (`divFullExact`): the exact quotient of numbers, the fault of
a zero divisor, no rule for an infinity or NaN. -/
def divFullE : List Value → Exec Value
  | [a, b] => (approxVal divFullI [a, b]).getD (.error .noRule)
  | _ => .error .noRule

/-- The reading at pc 600: the exact quotient, or no rule. -/
theorem exec_divFull {t : TState} (hpc : t.pc = 600) {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA Assumptions.all L g t (.float { divFullI with dsts := [some d], srcs := [a, b] }) =
      (divFullE [va, vb]).map fun v => PTX.next (setReg t d v) := by
  set op : Op := .float { divFullI with dsts := [some d], srcs := [a, b] } with hop
  have hseg : SegFreePc Assumptions.all t.pc := Kernels.InklingRelDecode.Proof.segFree (by
    rw [hpc]; decide +kernel)
  have h1 : Assumptions.idealArith.localRule L g t op = none :=
    idealReal_localRule_none fun f h => by simp [hop, FloatForm.ofOp] at h
  have h2 : Assumptions.approx.localRule L g t op = none :=
    approxExact_localRule_none fun f h => by simp [hop, ApproxForm.ofOp] at h
  have h4 : Assumptions.lg2Exact.localRule L g t op = none := by
    simp [Assumptions.lg2Exact, Assumptions.lg2Sites, hpc]
  have h5 : Assumptions.divFullExact.localRule L g t op =
      (approxVal divFullI [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [Assumptions.divFullExact, Assumptions.divFullSites, hpc, hop, approxVal,
      readFinite_of ha.2, readFinite_of hb.2, bindRead_map]
    simp
    rcases finiteVal va with _ | (e | x)
    · rfl
    · rfl
    rcases finiteVal vb with _ | (e | y)
    · rfl
    · rfl
    simp only [bindRead]
    split_ifs <;> rfl
  have h3 : (Assumptions.swExp2 kernel).localRule L g t op = none := rfl
  have h6 : Assumptions.negExact.localRule L g t op = none := by
    simp [Assumptions.negExact, Assumptions.negSites, hpc]
  have h7 : Assumptions.bf16Exact.localRule L g t op = none := by
    simp [Assumptions.bf16Exact, hop]
  rw [hseg.exec rfl]
  simp only [execLocalRule, Assumptions.all, List.findSome?, h1, h2, h3, h4, h5, h6, h7]
  have h8 : Assumptions.commitOrder.localRule L g t op = none := rfl
  have h9 : Assumptions.pollAgree.localRule L g t op = none := rfl
  have h10 : Assumptions.setMaxNRegSync.localRule L g t op = none := rfl
  have h11 : Assumptions.inputReadOnly.localRule L g t op = none := rfl
  simp only [h8, h9, h10, h11]
  cases hv : approxVal divFullI [va, vb] with
  | some r => simp [divFullE, hv]
  | none => simp [divFullE, hv, hop]; rfl

theorem rule_divFull {d : Nat} {a b : Opnd} (pc : Nat) (hp : pc = 600)
    (hq : [a, b].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp divFullI d [a, b]) d (regsOf [a, b]) (fF divFullE [a, b])).Rule
      Assumptions.all L g t :=
  fun _ ht => XItem.float_rule hq fun _ hW => exec_divFull (by omega) (hW a (by simp))
    (hW b (by simp))

theorem emu_lt {pc : Nat} (h : pc < 1913) : Assumptions.emuSites.contains pc = false := by
  rw [Bool.eq_false_iff]
  intro h'
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h'
  obtain ⟨i, hi, he⟩ := h'
  omega

theorem segFreeLt {pc : Nat} (h : pc < 1913) : SegFreePc Assumptions.all pc :=
  Kernels.InklingRelDecode.Proof.segFree (emu_lt h)

/-- `mul.f32` of a run's pc outside the single-instruction readings. -/
theorem rule_mulC {d : Nat} {a b : Opnd} (pc : Nat) (hp : intPc pc = true)
    (hq : [a, b].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (mulI false) d [a, b]) d (regsOf [a, b]) (fF (mulL false) [a, b])).Rule
      Assumptions.all L g t := by
  intro t ht
  simp only [intPc, decide_eq_true_eq] at hp
  have h := forms_at (L := L) (g := g) (f := .mul .f32) (by simp [idealForms]) (pc := pc)
    (emu_lt (by omega)) (by omega) (by omega) (by omega) t ht
  exact XItem.mul_rule h.1 h.2 hq

/-- The reading at pc 807: the negation of the extended real, Core's outcome for a NaN. -/
theorem exec_neg {t : TState} (hpc : t.pc = 807) {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocalA Assumptions.all L g t (.float { negI false with dsts := [some d], srcs := [a] }) =
      (negE false va).map fun v => PTX.next (setReg t d v) := by
  set op : Op := .float { negI false with dsts := [some d], srcs := [a] } with hop
  have hseg : SegFreePc Assumptions.all t.pc := Kernels.InklingRelDecode.Proof.segFree (by
    rw [hpc]; decide +kernel)
  have h1 : Assumptions.idealArith.localRule L g t op = none :=
    idealReal_localRule_none fun f h => by
      simp [hop, FloatForm.ofOp] at h
      subst h
      decide
  have h2 : Assumptions.approx.localRule L g t op = none :=
    approxExact_localRule_none fun f h => by simp [hop, ApproxForm.ofOp] at h
  have h3 : (Assumptions.swExp2 kernel).localRule L g t op = none := rfl
  have h4 : Assumptions.lg2Exact.localRule L g t op = none := by
    simp [Assumptions.lg2Exact, Assumptions.lg2Sites, hpc]
  have h5 : Assumptions.divFullExact.localRule L g t op = none := by
    simp [Assumptions.divFullExact, Assumptions.divFullSites, hpc]
  have h6 : Assumptions.negExact.localRule L g t op = (idealNeg va).map
      (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [Assumptions.negExact, Assumptions.negSites, hpc, hop, idealNeg, ha.2,
      bindRead_map]
    simp
    rcases readEReal .f32 va with _ | (e | x) <;> rfl
  have h7 : Assumptions.bf16Exact.localRule L g t op = none := by
    simp [Assumptions.bf16Exact, hop]
  have h8 : Assumptions.commitOrder.localRule L g t op = none := rfl
  have h9 : Assumptions.pollAgree.localRule L g t op = none := rfl
  have h10 : Assumptions.setMaxNRegSync.localRule L g t op = none := rfl
  have h11 : Assumptions.inputReadOnly.localRule L g t op = none := rfl
  rw [hseg.exec rfl]
  simp only [execLocalRule, Assumptions.all, List.findSome?, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11]
  unfold negE
  cases hv : idealNeg va with
  | some r => simp
  | none => simp [hop, execLocal_neg_core ha]

theorem rule_negC {d : Nat} {a : Opnd} (pc : Nat) (hp : pc = 807)
    (hq : [a].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (negI false) d [a]) d (regsOf [a]) (fF (negL false) [a])).Rule
      Assumptions.all L g t :=
  fun _ ht => XItem.float_rule hq fun _ hW => exec_neg (by omega) (hW a (by simp))

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax

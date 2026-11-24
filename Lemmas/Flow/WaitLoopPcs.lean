-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollFacts
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # Wait loops at listed positions

A proof tool. `Kernel.waitLoopsOk` checks every position of a kernel, reading the code at each
(quadratic in its length). For a long kernel the polls' positions are listed instead: every
`mbarrier.try_wait` is at a listed position (`OpPcsFast`, one pass) and each listed position heads
a wait loop (`waitLoop`, three reads each) whose predicate is read nowhere but in its own branch
(`Kernel.waitLoopPcs`). Then every poll is a canonical spin
(`Kernel.canonicalSpin_of_waitLoopPcs`). -/

namespace PTX

open PTX.Flow

noncomputable section

/-- Whether an instruction is an `mbarrier.try_wait`. -/
def Flow.pollOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

namespace Kernel

/-- Each listed position heads a wait loop that no branch enters, and each listed poll's predicate
is read nowhere but in the loop's branch (DEP-CANONICAL-SPIN). -/
def waitLoopPcs (K : Kernel) (l : List Nat) : Bool :=
  l.all fun pc => waitLoop K.code pc && !K.targeted (pc + 1) && !K.targeted (pc + 2) &&
    (match K.pollReg pc with
      | some p => K.spinPred p
      | none => true)

/-- **Every poll at a listed position is a canonical spin**, exiting to its loop's exit: the list
holds every poll (`OpPcsFast`) and each listed position heads a wait loop whose branches no branch
targets and which reads its predicate nowhere but in its branch. -/
theorem canonicalSpin_of_waitLoopPcs {K : Kernel} {l : List Nat}
    (hpcs : OpPcsFast K.code pollOp l = true) (hl : K.waitLoopPcs l = true)
    {pc : Nat} {ins : Instr} (hc : K.code[pc]? = some ins) {p base : Nat} {off : Int}
    {par : Opnd} {acq : Bool} {sc : MbarScope} (ho : ins.op = .mbarWait p base off par acq sc) :
    ∃ exit, K.CanonicalSpin pc exit := by
  have hp : pollOp ins.op = true := by rw [ho]; rfl
  have hmem := OpPcsFast.mem hpcs hc hp
  unfold waitLoopPcs at hl
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hl
  obtain ⟨⟨⟨hw, ht1⟩, ht2⟩, hs⟩ := hl pc hmem
  obtain ⟨gd, op⟩ := ins
  simp only at ho
  subst ho
  cases hgd : gd with
  | some g =>
    simp only [waitLoop, hc, hgd, Bool.false_eq_true] at hw
  | none =>
    have hpoll : K.pollReg pc = some p := by simp only [Kernel.pollReg, hc, hgd]
    rw [hpoll] at hs
    exact canonicalSpin_of_waitLoop hw (by simpa only [hgd] using hc) ht1 ht2 hs

end Kernel

end

end PTX

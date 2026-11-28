-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Pred
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyMath
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
def copyVote (b : Fin 3) (j : Fin 4) :=
  ([[58,60,61,62],[68,69,70,71],[77,78,79,80]][b.val]!)[j.val]!
def copyGuard (b : Fin 3) (j : Fin 4) := [54,64,73][b.val]! + j.val
private def start (b : Fin 3) (j : Fin 4) := if b=0 ∧ j=0 then 205 else pelPc b j+1

private theorem comparison (n : Nat) (bound : n<128) :
    PTX.compare .lt .u 32 (truncBits 32 (BitVec.ofNat 64 n))
      (truncBits 32 (BitVec.ofInt 64 64)) = decide (n<64) := by
  simp [PTX.compare,truncBits]
  omega

private theorem initial {Q L g w d} :
    Seg kernel Assumptions.all L g 1 204 ((58,.pred d.elected)::facts Q L g w d 203)
      205 (facts Q L g w d 205) := by
  intro t ht
  seg_fp ht using exact congrArg Value.pred (comparison _ (Nat.mod_lt _ (by decide)))

private theorem keys : ∀ b j,
    (b=0 ∧ j=0) ∨ (ctlLive (start b j)).all (fun r =>
      decide (r=copyVote b j ∨ r ∈ ctlLive (pelPc b j))) := by decide +kernel

private theorem project {Q L g w d} (b j) (h : ¬(b=0 ∧ j=0)) :
    SegU kernel Assumptions.all L g (pelPc b j+1)
      ((copyVote b j,.pred d.elected)::facts Q L g w d (pelPc b j))
      (start b j) (facts Q L g w d (start b j)) := by
  intro t ht
  apply Or.inl
  refine ⟨t,.refl,?_⟩
  rw [start,ite_eq_right h]
  obtain ⟨_,_,_,_,won,regs⟩ := id ht
  apply ht.mono
  apply holds_of_pointwise
  intro r hr
  have key := of_decide_eq_true (List.all_eq_true.mp ((keys b j).resolve_left h) r
    (by simpa [start,h] using hr))
  rcases key with rfl|old
  · have val : valueOf Q L g w d (copyVote b j) = .pred d.elected := by
      fin_cases b <;> fin_cases j <;> rfl
    rw [val]
    exact won
  · exact holds_mem regs (mem_factsFrom old)

private theorem guard_span {Q L g w d} (b : Fin 3) (j : Fin 4) :
    Seg kernel Assumptions.all L g 1 (start b j) (facts Q L g w d (start b j))
      (start b j+1) (facts Q L g w d (start b j+1)) := by
  fin_cases b <;> fin_cases j <;> intro t ht <;> seg_fp ht using rfl

theorem copy_span {Q L g w} (d : D) (b : Fin 3) (j : Fin 4) :
    SegU kernel Assumptions.all L g (pelPc b j+1)
      ((copyVote b j,.pred d.elected)::facts Q L g w d (pelPc b j))
      (ptcPc b j) (facts Q L g w d (ptcPc b j)) := by
  apply SegU.comp (b := start b j) (G := facts Q L g w d (start b j))
  · by_cases h : b=0 ∧ j=0
    · obtain ⟨rfl,rfl⟩ := h
      exact SegU.of_seg initial
    · exact project b j h
  · have stage : start b j+1=copyMathPc b j := by fin_cases b <;> fin_cases j <;> rfl
    apply (SegU.of_seg (guard_span b j)).comp
    rw [stage]
    exact copy_math b j

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

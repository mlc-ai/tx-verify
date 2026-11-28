-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.StepsTest
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value}

def afterPacket (i n a b : Value) : D :=
  ⟨if r32 (bits i + 1) = bits n then .endBar else .poll, nextCounter i, n, a, b⟩

theorem finish_last (s : Site) (i n a b : Value) :
    finishPair ⟨s,i,n,a,b⟩ 3 = afterPacket i n a b := rfl

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
/-- Both ways to finish the final pair cross the same increment and branch. -/
theorem loop_span (i n a b : Value) :
    let regs := inputs Q L g rest
    let V := loopValue L g w regs ⟨.poll,i,n,a,b⟩
    let C := code L g w regs
    SegU kernel Assumptions.all L g 2413 (factsFrom (Flow.live 2413) V)
      (C.pc (afterPacket i n a b)) (C.facts (afterPacket i n a b)) := by
  intro regs V C
  let N := loopValue L g w regs ⟨.poll,nextCounter i,n,a,b⟩
  have advance := (counter_span (L := L) (g := g) i V rfl).comp
    ((SegU.of_seg (cursors_span i n a b)).comp (test_span i n N rfl rfl))
  apply advance.comp
  by_cases h : r32 (bits i + 1) = bits n
  · simp only [h, not_true_eq_false, decide_false, afterPacket, ↓reduceIte]
    apply SegU.of_seg (n := 1)
    intro t ht
    dsimp only [C, V, N, code] at ht ⊢
    have hfalse : decide (bits n ≠ bits n) = false := decide_eq_false (not_not_intro rfl)
    simp only [h, hfalse] at ht
    seg_fp ht using rfl
  · simp only [h, not_false_eq_true, decide_true, afterPacket, ↓reduceIte]
    refine SegU.comp ?_ (ring_head (L := L) (g := g) (w := w) (regs := regs) (nextCounter i) n a b)
    apply SegU.of_seg (n := 1)
    intro t ht
    dsimp only [V, N, loopFacts] at ht ⊢
    rw [decide_eq_true h] at ht
    seg_fp ht using rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Loader

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
public import Kernels.InklingRelDecode.Proof.Lib.IntStep
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {L : Launch} {g : Nat} {w : Value} {regs : Nat → Value} (i n a b : Value)

abbrev loopFacts (pc : Nat) := factsFrom (Flow.live pc) (loopValue L g w regs ⟨.poll,i,n,a,b⟩)

/-- The eight instructions following mul.hi keep both paths to the loop head in one
successor family. The raw counter is used only by the first instruction. -/
theorem ring_head :
    SegU kernel Assumptions.all L g 2365 (loopFacts (L := L) (g := g) (w := w) (regs := regs)
      i n a b 2365) 2374 ((code L g w regs).facts ⟨.poll,i,n,a,b⟩) := by
  let F := loopFacts (L := L) (g := g) (w := w) (regs := regs) i n a b 2365
  let high := r32 (BitVec.ofInt 64 (toSigned 32 (r32 (bits i)) * 1431655766 / 2 ^ 32))
  have hm : (1905, i) ∈ F := mem_factsFrom
    (val := loopValue L g w regs ⟨.poll,i,n,a,b⟩) (show 1905 ∈ Flow.live 2365 by decide)
  have mulHi : SegU kernel Assumptions.all L g 2365 F 2366 ((597,.bits 32 high) :: F) := by
    apply Lib.scalarStepU Flow.code_2365 rfl rfl (by decide)
    · intro t u hF he
      have hImm : readBits L g t 32 (.imm 1431655766) = .ok (i32 1431655766) := rfl
      simp only [execInt, DType.width, hImm, bind, Except.bind, pure, Except.pure] at he
      cases h : readBits L g t 32 (.reg 1905) <;> rw [h] at he <;> try contradiction
      rw [Lib.readBits_eq_pattern (holds_mem hF hm) h] at he
      have hid : r32 (bits i) = bits i := truncBits_idem ..
      change u = PTX.next (setReg t 597 (.bits 32 high))
      dsimp only [high]
      rw [hid]
      exact (Except.ok.inj he).symm
    · intro R hR
      exact ⟨Function.update_self .., holds_update hR (by fact_free)⟩
  apply mulHi.comp
  apply SegU.of_seg (n := 8)
  intro t ht
  dsimp only [F, loopFacts, code] at ht ⊢
  seg_fp ht using rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Loader

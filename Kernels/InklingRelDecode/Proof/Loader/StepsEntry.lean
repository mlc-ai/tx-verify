-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Inputs
public import Lemmas.Flow.SegChain
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value} (i n a b : Value)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The loop prologue computes shared strides, CTA coordinates, and the block-table row
before using the counter for the first time. -/
theorem setup_span :
    let regs := inputs Q L g rest
    Seg kernel Assumptions.all L g 11 2349
      ((19, .pred false) :: (code L g w regs).facts ⟨.beginBar,i,n,a,b⟩)
      2360 (factsFrom (Flow.live 2360) (entryValue Q L g w rest i n a b)) := by
  intro regs t ht
  dsimp only [regs, code] at ht
  let z := r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .z))
  let y := r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .y))
  let col := mul32 (r32 (BitVec.ofNat 64 (Q.headCols % 2 ^ 32))) y
  let V := entryValue Q L g w rest i n a b
  have hbt : V 1950 = .bits 64 (wide (mul32 (r32 (BitVec.ofNat 64 (Q.strideBt % 2 ^ 32))) z)
      (BitVec.ofNat 64 Q.btBase)) := rfl
  have hrow : V 470 = .bits 32 (mul32 (r32 (BitVec.ofNat 64 (Q.headRows % 2 ^ 32))) y) := rfl
  have hc : V 583 = .bits 32 col := rfl
  have hc1 : V 586 = .bits 32 (addi col 64) := rfl
  have hc2 : V 588 = .bits 32 (addi col 128) := rfl
  have hc3 : V 590 = .bits 32 (addi col 192) := rfl
  dsimp only [V] at hbt hrow hc hc1 hc2 hc3
  seg_fp ht using (first | rfl |
    (simp only [hbt, hrow, hc, hc1, hc2, hc3, wide, z, y, col, mul32, addi, r32,
      truncBits_idem, show intOf .s 32 (i32 4) = 4 by rfl] <;> rfl))

end
end PTX.Kernels.InklingRelDecode.Proof.Loader

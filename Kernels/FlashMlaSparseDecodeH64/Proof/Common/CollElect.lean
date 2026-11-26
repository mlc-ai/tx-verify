-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Seg
public import Lemmas.Kernel.Progress.Warp
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.Step.ElectFull

@[expose] public section

/-! # The elections' templates name the full warp

`elect_tmpl_shape`: the template of an `elect.sync` whose mask operand reads as all 32 lanes is
the election over the full mask (its static part is `.elect 4294967295`). For a state waiting at
one of the eight elections (pcs 16, 31, 1350, 1507, 1664, 1822, 1853, 2165), the mask register
holds `-1` by the role's facts (`startup_elect_tmpl`, `w0_elect_tmpl`, `mma_elect_tmpl`,
`tma_elect_tmpl`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The template of an election whose mask reads as the full warp** has the full static part. -/
theorem elect_tmpl_shape {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {dst : Option Nat} {p : Nat} {mask : Opnd} {ty : Option DType} {bits : BitVec 64}
    (hm : readBits L g t 32 mask = .ok bits) (hb : bits.toNat = 2 ^ 32 - 1) :
    Sched.tmplShape (eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some mask⟩)) =
      some (.elect 4294967295) := by
  have hl : PTX.laneOf L g < 32 := by simp only [PTX.laneOf]; omega
  have ht : (2 ^ 32 - 1).testBit (PTX.laneOf L g) = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hl
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hm, electMember, hb, ht, hl, and_self,
    ite_true, Sched.tmplShape]
  rfl

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

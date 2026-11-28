-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d

/-- The swizzle, computed once, up to the four packs of the query payload. -/
theorem seg_first_addr : Seg kernel Assumptions.all L g 7 515 (F 515) 522 (F 522) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_plain]
    seg_close [registerValue,queryBase,u32,b32])

/-- Compute the swizzle once, up to the four packs of the query payload. -/
theorem first_addr_522 : SegU kernel Assumptions.all L g 515 (F 514) 522 (F 522) :=
  SegU.comp (b := 515) (G := F 515) (cross (by decide +kernel : crossCheck 514 515 515))
    (SegU.of_seg seg_first_addr)

/-- Compute the swizzle once, then cross the four packs of the query payload. -/
theorem first_store_addr : SegU kernel Assumptions.all L g 515 (F 514) 526 (F 526) :=
  first_addr_522.comp (cross (by decide +kernel : crossCheck 522 522 526))

/-- Each remaining vector-store group adds a constant to the common swizzled address, up to the
four packs of its payload. -/
theorem seg_next_addr (i : Fin 7) :
    Seg kernel Assumptions.all L g 1 (527+6*i.val) (F (526+6*i.val))
      (528+6*i.val) (F (528+6*i.val)) := by
  fin_cases i <;> intro t ht <;> seg_fp ht using rfl

theorem next_addr_528 (i : Fin 7) :
    SegU kernel Assumptions.all L g (527+6*i.val) (F (526+6*i.val))
      (528+6*i.val) (F (528+6*i.val)) :=
  SegU.of_seg (seg_next_addr i)

/-- Each remaining vector-store group adds a constant to the common swizzled address.
The packed data registers may hold arbitrary values. -/
theorem next_store_addr (i : Fin 7) :
    SegU kernel Assumptions.all L g (527+6*i.val) (F (526+6*i.val))
      (532+6*i.val) (F (532+6*i.val)) := by
  have actual : ∀ j : Fin 7, crossCheck (528+6*j.val) (528+6*j.val) (532+6*j.val) := by
    decide +kernel
  exact (next_addr_528 i).comp (cross (actual i))

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

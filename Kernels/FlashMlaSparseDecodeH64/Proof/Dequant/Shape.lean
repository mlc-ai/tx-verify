-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Cnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeSetup
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeRows

@[expose] public section

/-! # Warpgroup 2's events by state

`shape`: the event a state of warpgroup 2 fires is its site's (`Ev.lean`), from the obligations
of `ShapeSetup.lean` and `ShapeRows.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The event kind a state of warpgroup 2 fires is its site's. -/
theorem shapeK (hp : Pre P L m) : (code P L g w).Shape (EvK L g) := by
  refine Code.Shape.of_at fun d => ?_
  cases hs : d.site with
  | smr => exact shapeAt_smr d hs
  | lenA => exact shapeAt_len d (.inl hs)
  | lenB => exact shapeAt_len d (.inr hs)
  | wq => exact shapeAt_wq d hs
  | wraw => exact shapeAt_wraw d hs
  | wsv => exact shapeAt_wsv d hs
  | scale r => exact shapeAt_scale d ⟨r, hs⟩
  | raw r i => exact shapeAt_raw d ⟨r, i, hs⟩
  | store r i => exact shapeAt_store d ⟨r, i, hs⟩
  | fpx => exact shapeAt_fpx d hs
  | arrD => exact shapeAt_arrD hp d hs
  | arrF => exact shapeAt_arrF hp d hs
  | bar => exact shapeAt_bar hp d hs
  | exit => exact shapeAt_exit d hs

/-- **The event a state of warpgroup 2 fires is the event of its site, at its pc.** -/
theorem shape (hp : Pre P L m) : (code P L g w).Shape (Ev L g) :=
  fun hat hi hc hf => ⟨fires_pc hf, shapeK hp hat hi hc hf⟩

/-- The counted machine's shape table. -/
theorem shape_counted (hp : Pre P L m) : (MC P L g w).Shape (fun d e => Ev L g d.1 e) :=
  Code.Shape.counted (shape hp)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant

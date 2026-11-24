-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeScanFirst
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeScanLoop
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeScanLoop2
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeScanSecond
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeSelect

@[expose] public section

/-! # Scheduler event shapes -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_scan (hp : Pre p L m) (d : D) (hk : d.k = 0) (k : Epilogue.Scan)
    (hs : d.site = .word k ∨ d.site = .down k ∨ (∃ j, d.site = .up k j) ∨ d.site = .total k ∨
      (∃ l, d.site = .vote l) ∨ (∃ l, d.site = .pre l) ∨ ∃ l, d.site = .tiles l) :
    (code p L g).ShapeAt (Ev p L g) d := by
  have h : (d.site = .word k ∨ d.site = .down k ∨
      (∃ j, d.site = .up k j) ∨ d.site = .total k) ∨
      ((∃ l, d.site = .vote l) ∨ (∃ l, d.site = .pre l) ∨ ∃ l, d.site = .tiles l) := by
    simpa only [or_assoc] using hs
  rcases h with h | h
  · cases k
    · exact @shapeAt_scanFirst p L m g hp d hk h
    · exact @shapeAt_scanLoop p L m g hp d hk h
    · exact @shapeAt_scanSecond p L m g hp d hk h
    · exact @shapeAt_scanLoop2 p L m g hp d hk h
  · exact @shapeAt_select p L m g hp d hk h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

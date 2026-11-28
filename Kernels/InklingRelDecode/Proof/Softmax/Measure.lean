-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow Control

/-- Execution order within the block, including the backward jump into P publication. -/
def Site.position : Site → Nat
  | .nxt j => j.val | .waitS => 64 | .shfl4 => 65 | .ldS => 66 | .waitLd => 67
  | .shfl5 => 68 | .shfl6 => 69 | .waitO => 70 | .bar22 => 71 | .shfl7 => 72
  | .shfl8 => 73 | .shfl9 => 74 | .shfl10 => 75 | .store10 => 76 | .bar23 => 77
  | .ldL => 78 | .shfl11 => 79 | .shfl12 => 80 | .ldO => 81 | .waitLdO => 82
  | .bar24 => 83 | .stO => 84 | .waitStO => 85 | .bar20 => 86 | .tmemSt => 87
  | .tmemWait => 88 | .bar21 => 89 | .arrive => 90 | _ => 0

def measure (e : Entry) (d : D) :=
  91*(e.limit-d.i) + match d.site with
    | .setMaxReg => 156 | .bar0 => 155 | .pre j => 154-j.val | .epilogue => 0
    | s => 90-s.position

theorem position_bound (s : Site) : s.position ≤ 90 := by
  cases s <;> simp only [Site.position] <;> omega

theorem measure_bound {e t d} (h : Inv e t d) : measure e d ≤ 91*2^31+156 := by
  have lim := h.entry.limitEq
  have small : e.limit < 2^31 := by split at lim <;> omega
  unfold measure
  generalize d.site = s
  cases s <;> dsimp only <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax

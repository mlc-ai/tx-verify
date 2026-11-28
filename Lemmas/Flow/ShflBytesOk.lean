-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TmplOkSync

@[expose] public section

/-! # A full-mask shuffle of any register of four bytes is not undefined behaviour

`shfl_imm_ok` for a source register that holds a word of four bytes, whatever its form (a bit
pattern, a number, a pair of halves): the template reads the register as it is. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

theorem shfl_bytes_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {mode : ShflMode} {d : Nat} {p : Option Nat} {r : Nat} {b c : Int} {v : Value}
    (hm : mode = .bfly ∨ mode = .idx) (hb : L.block % 32 = 0)
    (hr : t.regs r = some v) (hv : v.bytes = 4) (f : Fault) :
    eventTmpl A L g t (.warp { kind := .shfl mode, ty := some (.int .b 32),
                               dsts := some d :: (p.map some).toList,
                               srcs := [.reg r, .imm b, .imm c], mask := some (.imm (-1)) }) ≠
      .ub f := by
  have hrule : WarpInstr.rule { kind := .shfl mode, ty := some (.int .b 32),
                                dsts := some d :: (p.map some).toList,
                                srcs := [.reg r, .imm b, .imm c], mask := some (.imm (-1)) } =
      some .threadShfl := by
    rcases hm with rfl | rfl <;> cases p <;> rfl
  simp only [eventTmpl, warpTmpl, hrule, shflTmpl, readValue, readReg, hr, readBits, pure,
    Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 by decide]
  simp [hb, hv]

end

end PTX.Flow

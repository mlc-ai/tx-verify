-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop
public import Lemmas.Flow.TcTmpl
public import Lemmas.Flow.TmplOkOff

@[expose] public section

/-! # Templates of the worker sites that are not undefined behaviour

The immediate-operand barrier and the 512-column deallocation through an address register, as
`Lemmas/Flow/TmplOkMore.lean` does for the barriers with a thread count. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

theorem barSync_imm_ok {id : Nat} {al : Bool} (hid : id < 16) (f : Fault) :
    eventTmpl A L g t (.barSync (.imm id) al) ≠ .ub f := by
  have hid' : (truncBits 32 (BitVec.ofInt 64 (id : Int))).toNat = id := by
    simp [truncBits]; omega
  simp only [eventTmpl, barTmpl, readBits, pure, Except.pure, hid']
  simp [show ¬ 16 ≤ id by omega]

theorem tcDealloc_imm_ok {grp : CtaGroup} {ra : Nat} {v : Value} {x : BitVec 64}
    (hb : L.block % 32 = 0) (hra : t.regs ra = some v) (hv : v.regBits = some x) (f : Fault) :
    eventTmpl A L g t (.tcDealloc grp (.reg ra) (.imm 512)) ≠ .ub f := by
  simp only [eventTmpl, tcTmpl, readBits_regBits hra hv, hb, bind, Except.bind, pure, Except.pure]
  have h : readBits L g t 32 (.imm 512) = .ok (BitVec.ofNat 64 512) := rfl
  rw [h]
  simp [Tmem.validColumns, ofExec]

end
end PTX.Flow

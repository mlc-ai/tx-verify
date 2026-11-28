-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MemAl
import Lemmas.Flow.MemTmpl
import Lemmas.Flow.UbFree
import Lemmas.Flow.LoadShared

@[expose] public section

/-! # A weak store whose source value `storeValue` accepts is not undefined behaviour

`storeAl_ok` for a source register whose value need not have the element's size: `storeValue`
at the element's width truncates or accepts it (a packed pair of halves, a wider bit pattern). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **A weak store at an aligned effective address of a register `storeValue` accepts is no
undefined behaviour.** -/
theorem storeAl_sv_ok {a : MemAccess} {sp : Space} {base w r : Nat} {loc : Loc} {v x : Value}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hea : effAddr L g t sp base a.addr.off = .ok loc) (hw : a.elem.width / 8 ≠ 0)
    (hal : loc.addr % (a.elem.width / 8 * a.srcs.length) = 0)
    (hsrc : a.srcs[t.sub]? = some (.reg r)) (hv : t.regs r = some v)
    (hsv : storeValue a.elem.width v = .ok x) (f : Fault) :
    eventTmpl A L g t (.mem a) ≠ .ub f := by
  rw [eventTmpl, memTmpl_store hrule hs hb hk hsem]
  simp only [storeTmpl, hea, elemAcc, hw, hal, bind, Except.bind, false_or, ne_eq,
    not_true_eq_false, ↓reduceIte, pure, Except.pure, hsrc]
  simp [readValue, readReg, hv, pure, Except.pure, hsv]

end
end PTX.Flow

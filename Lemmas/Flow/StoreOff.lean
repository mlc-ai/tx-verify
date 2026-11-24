-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop
public import Lemmas.Flow.LoadShared

@[expose] public section

/-! # A shared vector store at a register plus an offset

`stv_ok` (`Lemmas/Flow/UbStop.lean`) with an immediate offset: element `t.sub` of a shared vector
store of 32-bit words at `[base + off]`, at an address aligned to the vector, of a register that
holds a four-byte value, is not undefined behaviour. Promoted from tml-fa4's
`Proof2/Lib/StoreOff.lean` (lane T1). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

theorem stv_off_ok {L : Launch} {g : Nat} {t : TState} {base : Nat} {off : Nat}
    {srcs : List Opnd} {a : Nat} {r : Nat} {ik : IType} {v : Value}
    (hr : t.regs base = some (b32 a)) (ha : a + off < 2 ^ 32)
    (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hal : (a + off) % (4 * srcs.length) = 0) (hs : srcs[t.sub]? = some (.reg r))
    (hv : t.regs r = some v) (hb : v.bytes = 4) (f : Fault) {A : List Assumption} :
    eventTmpl A L g t (.mem { kind := .store, space := some (.shared .cta), sem := .weak,
                              elem := .int ik 32, vec := srcs.length,
                              addr := ⟨.reg base 32, (off : Int)⟩, srcs := srcs }) ≠ .ub f := by
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik 32, vec := srcs.length,
                                addr := ⟨.reg base 32, (off : Int)⟩, srcs := srcs } =
      some .threadAccess := by
    rcases hn with h | h | h <;> cases ik <;> simp [MemAccess.rule,
      memTypeOk, DType.width, h]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)]
  have hsv : storeValue 32 v = .ok v := storeValue_of_bytes (w := 32) (by simpa using hb)
  have hea := effAddr_b32_off (L := L) (g := g) (t := t) (off := off) hr ha
  simp [storeTmpl, DType.width, hea, elemAcc, hal, hs, readValue, readReg, hv, hsv, bind,
    Except.bind, pure, Except.pure]

end

end PTX.Flow

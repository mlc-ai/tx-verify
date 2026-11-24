-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TmplOkMore
public import Lemmas.Flow.LoadShared

@[expose] public section

/-! # More instructions that are not undefined behaviour

A proof tool, beside `TmplOkMore`: a `bar.sync` whose id is a register below 16 with an
immediate count (`barSyncReg_ok`), a full-mask ballot of a predicate register (`vote_ok`), and
an element of a 32-bit shared vector store at a register plus an offset, aligned to the whole
vector, of a 4-byte register (`stv_off_ok`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- A `bar.sync` with the id in a register (below 16) and an immediate nonzero count multiple of
32. -/
theorem barSyncReg_ok {r id n : Nat} {al : Bool} (hr : t.regs r = some (b32 id)) (hid : id < 16)
    (_hn : n < 2 ^ 31) (hn32 : n % 32 = 0) (_hn0 : n ≠ 0) (f : Fault) :
    eventTmpl A L g t (.barSyncN (.reg r) (.imm n) al) ≠ .ub f := by
  have hn' : (BitVec.ofInt 64 (n : Int)).toNat = n := by simp; omega
  simp only [eventTmpl, barTmpl, readBits_b32' hr]
  simp only [readBits, pure, Except.pure, truncBits, BitVec.toNat_ofNat, hn']
  split_ifs <;> intro h <;> cases h <;> omega

/-- A full-mask ballot of a predicate register. -/
theorem vote_ok {d a : Nat} {neg : Bool} {b : Bool} (hb : L.block % 32 = 0)
    (ha : t.regs a = some (.pred b)) (f : Fault) :
    eventTmpl A L g t (.warp { kind := .vote .ballot neg, ty := some (.int .b 32),
                               dsts := [some d], srcs := [.reg a], mask := some (.imm (-1)) }) ≠
      .ub f := by
  rw [eventTmpl, warpTmpl_vote]
  simp only [voteTmpl, readBits, readPred, readReg, ha, bind, Except.bind, pure,
    Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 by decide]
  simp [hb]

/-- Element `t.sub` of a 32-bit shared vector store at a register plus an offset, the address
aligned to the whole vector, of a register holding a 4-byte value. -/
theorem stv_off_ok {base a n r : Nat} {off : Int} {srcs : List Opnd} {v : Value}
    {ik : IType} (hr : t.regs base = some (b32 a)) (hoff : off = (n : Int)) (ha : a + n < 2 ^ 32)
    (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hal : (a + n) % (4 * srcs.length) = 0) (hs : srcs[t.sub]? = some (.reg r))
    (hv : t.regs r = some v) (hb : v.bytes = 4) (f : Fault) :
    eventTmpl A L g t (.mem { kind := .store, space := some (.shared .cta), sem := .weak,
                              elem := .int ik 32, vec := srcs.length,
                              addr := ⟨.reg base 32, off⟩, srcs := srcs }) ≠ .ub f := by
  subst hoff
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik 32, vec := srcs.length,
                                addr := ⟨.reg base 32, (n : Int)⟩, srcs := srcs } =
      some .threadAccess := by
    rcases hn with h | h | h <;> cases ik <;> simp [MemAccess.rule,
      memTypeOk, DType.width, h]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)]
  simp only [DType.width, storeTmpl, effAddr_b32_off hr ha, bind, Except.bind, elemAcc]
  simp [hal, hs, readValue, readReg, hv, storeValue_of_bytes (w := 32) hb, pure, Except.pure]

end
end PTX.Flow

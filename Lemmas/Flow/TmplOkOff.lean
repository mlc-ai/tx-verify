-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop
public import Lemmas.Flow.LoadShared
public import Lemmas.Flow.RegBits

@[expose] public section

/-! # Allocations and loads at an offset whose event is not undefined behaviour

A proof tool, beside `UbStop`: a Tensor Memory allocation of 512 columns whose address word is
a 4-aligned shared word at a register plus an immediate offset (`tcAlloc_off_ok`, at its request
and at its address store), a 32-bit shared load of such a word (`ld_off_ok`), and a
deallocation of 512 columns at an address register whose value has a bit pattern
(`tcDealloc_regBits_ok`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- A Tensor Memory allocation of 512 columns into a 4-aligned shared word at a register plus
an offset is not undefined behaviour. -/
theorem tcAlloc_off_ok {grp : CtaGroup} {base nc a off : Nat} (hb : L.block % 32 = 0)
    (hr : t.regs base = some (b32 a)) (ha : a + off < 2 ^ 32) (h4 : (a + off) % 4 = 0)
    (hn : t.regs nc = some (b32 512)) (f : Fault) :
    eventTmpl A L g t (.tcAlloc grp base (off : Int) (.reg nc)) ≠ .ub f := by
  simp only [eventTmpl, tcTmpl, effAddr_b32_off hr ha, readBits_b32' hn, hb, bind, Except.bind,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 by decide]
  by_cases hs : t.sub = 0 <;> simp [Tmem.validColumns, h4, hs, ofExec]

/-- A 32-bit shared load of a 4-aligned word at a register plus an offset, at its first
sub-step, is not undefined behaviour. -/
theorem ld_off_ok {d base a off : Nat} {ik : IType} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) (h4 : (a + off) % 4 = 0) (hsub : t.sub = 0) (f : Fault) :
    eventTmpl A L g t (.mem { kind := .load, space := some (.shared .cta), sem := .weak,
                              elem := .int ik 32, addr := ⟨.reg base 32, (off : Int)⟩,
                              dsts := [some d] }) ≠ .ub f := by
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl)
    rfl rfl rfl (by simp)]
  simp [loadTmpl, MemAccess.regs, DType.width, effAddr_b32_off hr ha, elemAcc, h4, hsub, bind,
    Except.bind, pure, Except.pure]

/-- A Tensor Memory deallocation of 512 columns at an address register whose value has a bit
pattern is not undefined behaviour. -/
theorem tcDealloc_regBits_ok {grp : CtaGroup} {ra rn : Nat} {v : Value} {x : BitVec 64}
    (hb : L.block % 32 = 0) (hra : t.regs ra = some v) (hv : v.regBits = some x)
    (hrn : t.regs rn = some (b32 512)) (f : Fault) :
    eventTmpl A L g t (.tcDealloc grp (.reg ra) (.reg rn)) ≠ .ub f := by
  simp only [eventTmpl, tcTmpl, readBits_regBits hra hv, readBits_b32' hrn, hb, bind,
    Except.bind, pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 by decide]
  simp [Tmem.validColumns, ofExec]

end
end PTX.Flow

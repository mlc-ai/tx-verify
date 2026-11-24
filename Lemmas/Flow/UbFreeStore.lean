-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbFree
import Lemmas.Flow.LoadShared

@[expose] public section

/-! # A shared store through a register's word

A scalar shared store of a four-byte register through a 32-bit register whose word plus the offset
is 4-aligned is no undefined behaviour, whether or not the sum wraps (`st_word_ok`); `st_ok`
(`Lemmas/Flow/TmplOkMore.lean`) is the form that states the sum. -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

theorem st_word_ok {base r : Nat} {off : Int} {x : BitVec 64} {v : Value} {ik : IType}
    (hr : t.regs base = some (.bits 32 x)) (hal : (x.toNat + (off % 4).toNat) % 4 = 0)
    (hs : t.sub = 0) (hv : t.regs r = some v) (hb : v.bytes = 4) (f : Fault) :
    eventTmpl A L g t (.mem { kind := .store, space := some (.shared .cta), sem := .weak,
                              elem := .int ik 32, addr := ⟨.reg base 32, off⟩,
                              srcs := [.reg r] }) ≠ .ub f := by
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl)
    rfl rfl rfl (by simp)]
  have hal' : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 4 = 0 := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
    rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64)]
    simp only [Nat.reducePow, Nat.cast_ofNat]
    omega
  rw [show (DType.int ik 32).width = 32 from rfl]
  simp [storeTmpl, effAddr_shared32 hr, bind, Except.bind, elemAcc, hs, hal', readValue, readReg,
    hv, storeValue_of_bytes (w := 32) (by simpa using hb), pure, Except.pure]

end

end PTX.Flow

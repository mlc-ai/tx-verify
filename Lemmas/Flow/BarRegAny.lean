-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.BarReg

@[expose] public section

/-! # Named barriers with the barrier id in a register, any outcome

A proof tool. Every event `bar.arrive r, n` fires, with the barrier id in register `r` (a value
below 16) and an immediate thread count (a multiple of the warp size, neither zero nor the
block), is `bar id n` (arrive): the instruction has no other event (`fires_barArrive_reg_any`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}

theorem fires_barArrive_reg_any {r id n : Nat} {al : Bool} {o : Option TState}
    (hr : t.regs r = some (b32 id)) (hid : id < 16) (hn : n < 2 ^ 31) (hn32 : n % 32 = 0)
    (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hf : Fires pc (eventTmpl A L g t (.barArrive (.reg r) (.imm n) al)) e o) :
    e = ⟨pc, .bar id (some n) .arrive⟩ := by
  have himm : readBits L g t 32 (Opnd.imm (n : Int)) = .ok (BitVec.ofNat 64 n) := by
    simp only [readBits, truncBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
    omega
  simp only [eventTmpl, barTmpl, readBits_b32 hr (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show id < 2 ^ 64 by omega), himm,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)] at hf
  simp only [show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, hn0, hnb, or_self, ne_eq,
    not_false_eq_true, implies_true, and_self, Fires] at hf
  exact hf.1

end
end PTX.Flow

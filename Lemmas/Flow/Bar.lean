-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # Named barrier arrivals

A proof tool. A `bar.sync` with an explicit count fires the arrival on the barrier its register
names, with that count (`fires_barN`); a bulk commit fires a commit (`fires_bulkCommit`). -/

namespace PTX.Flow

open PTX.Proof

/-- A `bar.sync id, n` with `id` in a register and a count other than zero and the block size
fires the arrival on `id` with count `n`. -/
theorem fires_barN {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {r : Nat}
    {id n pc : Nat} {al : Bool} {e : Event} {o : Option TState} (hr : t.regs r = some (b32 id))
    (hid : id < 16) (hn : n < 2 ^ 32) (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hf : Fires pc (eventTmpl A L g t (.barSyncN (.reg r) (.imm n) al)) e o) :
    e = ⟨pc, .bar id (some n)⟩ := by
  have hid' : id < 2 ^ 32 := by omega
  simp only [eventTmpl, barTmpl, readBits_b32 hr hid'] at hf
  have himm : readBits L g t 32 (Opnd.imm (n : Int)) = .ok (BitVec.ofNat 64 n) := by
    simp only [readBits, truncBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
    omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show id < 2 ^ 64 by omega), himm,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)] at hf
  simp only [show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, hn0, hnb, or_self] at hf
  exact hf.1

/-- Such a `bar.sync id, n` is the arrival on `id` with count `n`, from every state with `id` in
its register. -/
theorem tmpl_barN {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {r : Nat}
    {id n : Nat} {al : Bool} (hr : t.regs r = some (b32 id)) (hid : id < 16) (hn : n < 2 ^ 32)
    (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block) :
    ∃ t', eventTmpl A L g t (.barSyncN (.reg r) (.imm n) al) = .bar id t' (some n) := by
  have hid' : id < 2 ^ 32 := by omega
  have himm : readBits L g t 32 (Opnd.imm (n : Int)) = .ok (BitVec.ofNat 64 n) := by
    simp only [readBits, truncBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
    omega
  simp only [eventTmpl, barTmpl, readBits_b32 hr hid', BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show id < 2 ^ 64 by omega), himm, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, hn0, hnb, or_self]
  exact ⟨_, rfl⟩

/-- A bulk commit fires a commit. -/
theorem fires_bulkCommit {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t .bulkCommit) e o) :
    e = ⟨pc, .bulkCommit⟩ :=
  hf.1

end PTX.Flow

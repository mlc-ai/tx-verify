-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Events
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # Loads from shared memory at an offset

A proof tool. A 32-bit `ld.shared` from a register holding a 32-bit address `a` plus an
offset reads the bytes at `a + off` of the thread's CTA (`fires_ld_shared`). Element `t.sub` of
a `ld.shared.v4.b32` at `a + off` is the four bytes at `a + off + 4 * t.sub`
(`fires_ld_shared_vec4`). -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}

theorem effAddr_b32_off {base a off : Nat} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) :
    effAddr L g t .shared base (off : Int) = .ok ⟨.shared, g / L.block, a + off⟩ := by
  have h64 : a < 18446744073709551616 := by omega
  have h64' : off < 18446744073709551616 := by omega
  have hs : a + off < 18446744073709551616 := by omega
  have h32 : a + off < 4294967296 := ha
  simp only [effAddr, sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind, pure,
    Except.pure]
  congr
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have ho : ((off : Int) % ((2 ^ 64 : Nat) : Int)).toNat = off := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
  rw [ho]
  simp only [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ha]

/-- A 32-bit shared load at `a + off` reads there and continues with the bytes it read. -/
theorem fires_ld_shared {d base a off : Nat} {ik : IType} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        addr := ⟨.reg base 32, (off : Int)⟩, dsts := [some d] })) e (some u)) :
    ∃ ac bs, e = ⟨pc, .rd ac bs⟩ ∧ ac.loc = ⟨.shared, g / L.block, a + off⟩ ∧
      u = afterLoad t [d] bs := by
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl) rfl
    rfl rfl rfl] at hf
  simp only [MemAccess.regs, DType.width, loadTmpl,
    effAddr_b32_off hr ha, bind, Except.bind, elemAcc, hs] at hf
  simp only [Bool.false_eq_true, ↓reduceIte] at hf
  split_ifs at hf
  all_goals first
    | (simp [throw, throwThe, MonadExceptOf.throw, Fires] at hf; done)
    | (exfalso; simp_all; done)
    | (obtain ⟨bs, -, rfl, hu⟩ := hf
       exact ⟨_, bs, rfl, by simp [Loc.at], Option.some.inj hu⟩)

/-- **Element `t.sub` of a four-element 32-bit shared load** at `a + off`: the vector's sixteen
bytes start at `a + off` of the thread's CTA, so the element reads the four bytes at
`a + off + 4 * t.sub`, and the successor state holds the bytes it read (`afterLoad`). -/
theorem fires_ld_shared_vec4 {d0 d1 d2 d3 base a off : Nat} {ik : IType}
    (hr : t.regs base = some (b32 a)) (hal : (a + off) % 16 = 0) (ha : a + off < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        vec := 4, addr := ⟨.reg base 32, (off : Int)⟩,
        dsts := [some d0, some d1, some d2, some d3] })) e (some u)) :
    ∃ ac bs, e = ⟨pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, a + off + 4 * t.sub⟩ ∧ ac.size = 4 ∧
      u = afterLoad t [d0, d1, d2, d3] bs := by
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl) rfl
    rfl rfl rfl] at hf
  simp only [MemAccess.regs, DType.width, loadTmpl,
    effAddr_b32_off hr ha, bind, Except.bind, Bool.false_eq_true, ↓reduceIte] at hf
  rw [elemAcc_ok (by decide) (by simpa using hal)] at hf
  obtain ⟨bs, -, rfl, hu⟩ := hf
  exact ⟨_, bs, rfl, by simp [Loc.at], rfl, Option.some.inj hu⟩

end PTX.Flow

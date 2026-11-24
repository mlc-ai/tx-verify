-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Store

@[expose] public section

/-! # The bytes a fired vector store writes

Element `t.sub` of a 32-bit shared vector store writes the bytes of the register its source
operand names (`fires_stv32_bytes`). -/

namespace PTX.Flow

open PTX.Proof

/-- **A vector store writes the bytes of its source register's value**: its own bytes, or the low
bytes of a wider one (`storeValue`). -/
theorem fires_stv32_bytes {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {base : Nat}
    {a : Nat} {srcs : List Opnd} {pc : Nat} {e : Event} {o : Option TState} {r : Nat} {v : Value}
    {ik : IType}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (hs : srcs[t.sub]? = some (.reg r))
    (hv : t.regs r = some v)
    (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        vec := srcs.length, addr := ⟨.reg base 32, 0⟩, srcs := srcs })) e o) :
    ∀ acc bs, e.kind = .wr acc bs → ∃ v', storeValue 32 v = .ok v' ∧ bs = v'.toBytes := by
  intro acc bs hk
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik 32, vec := srcs.length,
                                addr := ⟨.reg base 32, 0⟩, srcs := srcs } =
      some .threadAccess := by
    rcases hn with h | h | h <;> cases ik <;> simp [MemAccess.rule,
      memTypeOk, DType.width, h]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)] at hf
  simp only [DType.width, storeTmpl, effAddr_b32 hr ha, bind, Except.bind] at hf
  cases hea : elemAcc ⟨.shared, g / L.block, a⟩ (32 / 8) srcs.length t.sub with
  | error f =>
    simp only [hea, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok a' =>
    simp only [hea, hs, readValue, readReg, hv, pure, Except.pure] at hf
    rcases hsv : storeValue 32 v with f | v' <;> simp only [hsv] at hf
    · simp only [Fires] at hf
      rw [hf.1] at hk
      cases hk
    simp only [Fires] at hf
    rw [hf.1] at hk
    cases hk
    exact ⟨v', rfl, rfl⟩

end PTX.Flow

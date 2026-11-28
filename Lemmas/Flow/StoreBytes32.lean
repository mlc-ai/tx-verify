-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StoreValid

@[expose] public section

/-! # The bytes of a 32-bit shared store of one register

A proof tool. The write of a one-source 32-bit shared store carries the bytes of the stored
value, which is the source register's value after `storeValue`: a function of that value alone. -/

namespace PTX.Flow
open PTX PTX.Proof

/-- The bytes `storeValue` makes of a 32-bit source, none when it faults. -/
noncomputable def storedBytes (v : Value) : List Byte :=
  ((storeValue 32 v).toOption.map Value.toBytes).getD []

theorem fires_stv32_bytes1 {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {base : Nat}
    {a src : Nat} {v : Value} {pc : Nat} {e : Event} {o : Option TState} {ik : IType}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (hv : t.regs src = some v)
    (sub : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        vec := 1, addr := ⟨.reg base 32, 0⟩, srcs := [.reg src] })) e o) :
    ∀ acc bs, e.kind = .wr acc bs → bs = storedBytes v := by
  intro acc bs hk
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik 32, vec := 1,
                                addr := ⟨.reg base 32, 0⟩, srcs := [.reg src] } =
      some .threadAccess := by
    cases ik <;> simp [MemAccess.rule, memTypeOk, DType.width]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)] at hf
  simp only [DType.width, storeTmpl, effAddr_b32 hr ha, bind, Except.bind, sub,
    List.length_singleton] at hf
  cases hea : elemAcc ⟨.shared, g / L.block, a⟩ (32 / 8) 1 0 with
  | error f =>
    simp only [hea, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok a' =>
    simp only [hea, List.getElem?_cons_zero, readValue, readReg, hv] at hf
    rcases hsv : storeValue 32 v with f | v'
    all_goals simp only [pure, Except.pure, hsv] at hf
    · simp only [Fires] at hf
      rw [hf.1] at hk
      cases hk
    simp only [Fires] at hf
    rw [hf.1] at hk
    cases hk
    simp only [storedBytes, hsv]
    rfl

end PTX.Flow

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StoreLoc

@[expose] public section

/-! # The access and bytes of a scalar shared store

A proof tool. A scalar `st.shared` of width `w` whose base register holds the word `a` and whose
source register holds `v` writes the bytes of `storeValue w v` with an access of `w / 8` bytes at
`a + off` of the thread's CTA (`fires_st_val`). A `st.shared.b128` of a 16-byte source register
value `v` writes exactly `v.toBytes` and continues at the next instruction (`fires_st_val128`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A scalar shared store that continues writes `w / 8` bytes of its source register's value: the
value's own bytes when it is `w / 8` long, the low bytes of a wider one (`storeValue`). -/
theorem fires_st_val {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {w : Nat}
    {base a off src : Nat} {v : Value} {ik : IType} {pc : Nat} {e : Event}
    (hr : t.regs base = some (b32 a)) (ha : a + off < 2 ^ 32) (hs : t.sub = 0)
    (hv : t.regs src = some v)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik w,
        addr := ⟨.reg base 32, (off : Int)⟩, srcs := [.reg src] })) e (some u))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    ∃ v', storeValue w v = .ok v' ∧
      ∃ acc, e.kind = .wr acc v'.toBytes ∧ acc.loc = ⟨.shared, g / L.block, a + off⟩ ∧
        acc.size = w / 8 := by
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik w, addr := ⟨.reg base 32, (off : Int)⟩,
                                srcs := [.reg src] } = some .threadAccess := by
    rcases hw with rfl | rfl | rfl | rfl <;> cases ik <;> rfl
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)] at hf
  simp only [DType.width, storeTmpl, effAddr_b32_off hr ha, bind, Except.bind, elemAcc, hs,
    Nat.mul_zero] at hf
  split_ifs at hf
  · simp [Fires, throw, throwThe, MonadExceptOf.throw] at hf
  · simp only [pure, Except.pure, List.getElem?_singleton, readValue, readReg, ite_true] at hf
    simp only [hv] at hf
    cases hsv : storeValue w v with
    | error f => simp only [hsv, Fires] at hf; exact absurd hf.2 (by simp)
    | ok v' =>
      simp only [hsv, Fires] at hf
      exact ⟨_, rfl, _, by rw [hf.1], by simp [Loc.at], rfl⟩

/-- A `st.shared.b128` that continues writes exactly the bytes of its 16-byte aligned source
register value: a `.wr` of `v.toBytes` over sixteen bytes at `a + off` of the thread's CTA, after
which the thread is at the next instruction. -/
theorem fires_st_val128 {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {base a off src : Nat} {v : Value} {pc : Nat} {e : Event}
    (hr : t.regs base = some (b32 a)) (ha : a + off < 2 ^ 32) (hal : (a + off) % 16 = 0)
    (hs : t.sub = 0) (hv : t.regs src = some v) (hv16 : v.bytes = 16)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 128,
        addr := ⟨.reg base 32, (off : Int)⟩, srcs := [.reg src] })) e (some u)) :
    ∃ acc, e = ⟨pc, .wr acc v.toBytes⟩ ∧ acc.loc = ⟨.shared, g / L.block, a + off⟩ ∧
      acc.size = 16 ∧ u = next t := by
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int .b 128, addr := ⟨.reg base 32, (off : Int)⟩,
                                srcs := [.reg src] } = some .threadAccess := rfl
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)] at hf
  simp only [DType.width, storeTmpl, effAddr_b32_off hr ha, bind, Except.bind, hs] at hf
  rw [elemAcc_ok (by decide) (by simpa using hal)] at hf
  simp only [pure, Except.pure, List.getElem?_singleton, readValue, readReg, ite_true, hv] at hf
  rw [storeValue_of_bytes (w := 128) (v := v) (by omega)] at hf
  simp only [Fires] at hf
  obtain ⟨rfl, hu⟩ := hf
  exact ⟨_, rfl, by simp [Loc.at], rfl,
    by rw [Option.some.inj hu]; simp [afterStore, hs, next]⟩

end
end PTX.Flow

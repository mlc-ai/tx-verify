-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Store
public import Lemmas.TensorStore.TensorStoreCompleteConsistentValidity

@[expose] public section

/-! # What a fired store event records

A tile tensor store fired by its instruction has a valid specification (`fires_cpTensorStore_form`),
and a 32-bit shared vector store writes as many bytes as its footprint (`fires_stv32_len`). -/

namespace PTX.Flow

open PTX.Proof

/-- A tile tensor store's specification is valid, has no row coordinates and has the instruction's
reduction. -/
theorem fires_cpTensorStore_form {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd}
    {reduce : Option AtomOp} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy .tile reduce)) e o) :
    ∀ a s, e.kind = .tensorStore a s →
      TensorStore.Valid (g / L.block) s ∧ s.rows = none ∧ s.reduce = reduce := by
  intro a s hk
  simp only [eventTmpl, tensorStoreTmpl] at hf
  cases hs : tensorStoreSpec L g t map cs src off policy .tile reduce with
  | error f =>
    simp only [hs, bind, Except.bind, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok r =>
    obtain ⟨a', s'⟩ := r
    simp only [hs, bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
    obtain ⟨-, -, -, -, -, hrows, hred⟩ := tensorStoreSpec_ok hs
    exact ⟨TensorStoreValidity.tile_valid hs, hrows.mpr rfl, hred⟩

/-- A stored value has the store's size in bytes (`storeValue`). -/
theorem storeValue_toBytes_length {w : Nat} {v v' : Value} (h : storeValue w v = .ok v') :
    v'.toBytes.length = w / 8 := by
  unfold storeValue at h
  split at h
  · rename_i hb
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [Value.toBytes, hb]
  · split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [Value.toBytes, Value.bytes]
      · cases h
    · cases h

/-- A write of element `t.sub` of a 32-bit shared vector store has four bytes. -/
theorem fires_stv32_len {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {base : Nat}
    {a : Nat} {srcs : List Opnd} {pc : Nat} {e : Event} {o : Option TState} {ik : IType}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32)
    (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        vec := srcs.length, addr := ⟨.reg base 32, 0⟩, srcs := srcs })) e o) :
    ∀ acc bs, e.kind = .wr acc bs → bs.length = 4 := by
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
    simp only [hea] at hf
    rcases hs : srcs[t.sub]? with _ | op <;> simp only [hs] at hf
    · simp only [Fires] at hf
      rw [hf.1] at hk
      cases hk
    rcases hv : readValue L g t 32 op with f | v <;> simp only [hv] at hf
    · simp only [Fires] at hf
      rw [hf.1] at hk
      cases hk
    rcases hsv : storeValue 32 v with f | v' <;> simp only [hsv] at hf
    · simp only [Fires] at hf
      rw [hf.1] at hk
      cases hk
    simp only [Fires] at hf
    rw [hf.1] at hk
    cases hk
    exact storeValue_toBytes_length hsv

/-- A 32-bit shared vector store fires a write or undefined behaviour. -/
theorem fires_stv32_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {base : Nat}
    {a : Nat} {srcs : List Opnd} {pc : Nat} {e : Event} {o : Option TState} {ik : IType}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32)
    (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        vec := srcs.length, addr := ⟨.reg base 32, 0⟩, srcs := srcs })) e o) :
    (∃ acc bs, e.kind = .wr acc bs) ∨ ∃ f, e.kind = .ub f := by
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
    exact .inr ⟨f, by rw [hf.1]⟩
  | ok a' =>
    simp only [hea] at hf
    rcases hs : srcs[t.sub]? with _ | op <;> simp only [hs] at hf
    · simp only [Fires] at hf
      exact .inr ⟨_, by rw [hf.1]⟩
    rcases hv : readValue L g t 32 op with f | v <;> simp only [hv] at hf
    · simp only [Fires] at hf
      exact .inr ⟨_, by rw [hf.1]⟩
    rcases hsv : storeValue 32 v with f | v' <;> simp only [hsv] at hf
    · simp only [Fires] at hf
      exact .inr ⟨_, by rw [hf.1]⟩
    simp only [Fires] at hf
    exact .inl ⟨_, _, by rw [hf.1]⟩

end PTX.Flow

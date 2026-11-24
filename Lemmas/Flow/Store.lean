-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Events
public import Lemmas.Flow.NotTensor
public import Lemmas.Tensor.TensorMap

@[expose] public section

/-! # Vector stores to shared memory

A proof tool. Element `j` of a 32-bit vector store to a shared address held in a register
writes the four bytes at that address plus `4 j` (`fires_stv32`). -/

namespace PTX.Flow

open PTX.Proof

/-- A write of element `t.sub` of a 32-bit shared vector store from address `a`. -/
theorem fires_stv32 {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {base : Nat}
    {a : Nat} {srcs : List Opnd} {pc : Nat} {e : Event} {o : Option TState} {ik : IType}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32)
    (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        vec := srcs.length, addr := ⟨.reg base 32, 0⟩, srcs := srcs })) e o) :
    ∀ acc bs, e.kind = .wr acc bs →
      acc.loc = ⟨.shared, g / L.block, a + 4 * t.sub⟩ ∧ acc.size = 4 := by
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
    unfold elemAcc at hea
    split_ifs at hea
    all_goals simp only [pure, Except.pure, Except.ok.injEq] at hea
    all_goals subst hea
    all_goals exact ⟨by simp [Loc.at], rfl⟩

/-- A tensor store's map, descriptor and shared source are its operands'. -/
theorem fires_cpTensorStore_spec {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd}
    {mode : TensorMode} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy mode reduce)) e o) :
    ∀ a s, e.kind = .tensorStore a s → tensorMapAddress L g t map = .ok a ∧
      (∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ s.descriptor = mode.transfer d) ∧
      sharedEffAddr L g t false src off = .ok s.sharedBase := by
  intro a s hk
  simp only [eventTmpl, tensorStoreTmpl] at hf
  cases hs : tensorStoreSpec L g t map cs src off policy mode reduce with
  | error f =>
    simp only [hs, bind, Except.bind, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok r =>
    obtain ⟨a', s'⟩ := r
    simp only [hs, bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
    unfold tensorStoreSpec at hs
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hs
    rcases hm : tensorMap L g t map cs mode with f | ⟨a'', outer, d⟩ <;> rw [hm] at hs
    · cases hs
    obtain ⟨hma, hd, -, -⟩ := tensorMap_ok hm
    rcases hsrc : sharedEffAddr L g t false src off with f | sl <;> simp only [hsrc] at hs
    all_goals repeat' (split at hs <;> (try (cases hs; done)))
    all_goals (cases hs; exact ⟨hma, ⟨d, hd, rfl⟩, rfl⟩)

/-- A tensor store instruction fires a tensor store or undefined behaviour. -/
theorem fires_cpTensorStore_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd}
    {mode : TensorMode} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy mode reduce)) e o) :
    (∃ a s, e.kind = .tensorStore a s) ∨ ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, tensorStoreTmpl] at hf
  cases hs : tensorStoreSpec L g t map cs src off policy mode reduce with
  | error f =>
    simp only [hs, bind, Except.bind, ofExec, Fires] at hf
    exact .inr ⟨f, by rw [hf.1]⟩
  | ok r =>
    obtain ⟨a', s'⟩ := r
    simp only [hs, bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
    exact .inl ⟨a', s', by rw [hf.1]⟩

/-- A swizzled byte stays within its 128-byte row. -/
theorem swizzle_offset_bounds (mode : TensorSwizzle.Mode) (base n : Nat) :
    128 * (n / 128) ≤ TensorSwizzle.offset mode base n ∧
      TensorSwizzle.offset mode base n < 128 * (n / 128) + 128 := by
  unfold TensorSwizzle.offset
  have h1 := (TensorSwizzle.chunk mode base (n / 128) (BitVec.ofNat 3 (n / 16))).isLt
  have h2 : n % 16 < 16 := Nat.mod_lt _ (by decide)
  constructor <;> omega

end PTX.Flow

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Store
public import Lemmas.Flow.TensorLoadFacts
public import Lemmas.TensorStore.TensorStoreThread

@[expose] public section

/-! # The fields of a tensor store

A proof tool, the store counterpart of `TensorLoadFacts`. A tensor store instruction that fires a
tensor store issues the specification `tensorStoreSpec` computes (`fires_cpTensorStore_ok`),
whose origin is the low 32 bits of its coordinate operands (`tensorStoreSpec_origin_all`); for
four coordinate registers holding 32-bit values below `2 ^ 31`, those values
(`tensorStoreSpec_origin_regs`). Its source is a 32-bit shared address register plus the
immediate offset in the issuer's CTA (`sharedEffAddr_b32`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A firing tensor store issues the specification `tensorStoreSpec` computes. -/
theorem fires_cpTensorStore_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd}
    {mode : TensorMode} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy mode reduce)) e o)
    {a : Nat} {s : TensorStore.Spec} (hk : e.kind = .tensorStore a s) :
    tensorStoreSpec L g t map cs src off policy mode reduce = .ok (a, s) := by
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
    rfl

/-- The origin of a tensor store is its coordinate operands' low 32 bits. -/
theorem tensorStoreSpec_origin_all {L : Launch} {g : Nat} {t : TState} {map : Opnd}
    {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {a : Nat} {s : TensorStore.Spec} {vs : List (BitVec 64)}
    (h : tensorStoreSpec L g t map cs src off policy mode reduce = .ok (a, s))
    (hvs : cs.mapM (readBits L g t 32) = .ok vs) :
    ∀ i : Fin (s.outer + 1), s.origin i = (BitVec.ofNat 32 (vs.getD i.val 0).toNat).toInt := by
  unfold tensorStoreSpec at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    hvs] at h
  rcases hm : tensorMap L g t map cs mode with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  dsimp only at h
  rcases hd : sharedEffAddr L g t false src off with f | dl <;> simp only [hd] at h
  all_goals repeat' (split at h <;> (try (cases h; done)))
  all_goals cases h
  all_goals intro i
  all_goals rfl

/-- The origin of a four-coordinate tensor store whose coordinate registers hold 32-bit values
below `2 ^ 31`: those values. -/
theorem tensorStoreSpec_origin_regs {L : Launch} {g : Nat} {t : TState} {map : Opnd}
    {src r0 r1 r2 r3 x0 x1 x2 x3 : Nat} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {a : Nat} {s : TensorStore.Spec}
    (h : tensorStoreSpec L g t map [.reg r0, .reg r1, .reg r2, .reg r3] src off policy mode
      reduce = .ok (a, s))
    (h0 : t.regs r0 = some (b32 x0)) (h1 : t.regs r1 = some (b32 x1))
    (h2 : t.regs r2 = some (b32 x2)) (h3 : t.regs r3 = some (b32 x3)) (hx0 : x0 < 2 ^ 31)
    (hx1 : x1 < 2 ^ 31) (hx2 : x2 < 2 ^ 31) (hx3 : x3 < 2 ^ 31) :
    ∀ i : Fin (s.outer + 1), s.origin i = ([x0, x1, x2, x3].getD i.val 0 : Nat) := by
  have hv := tensorStoreSpec_origin_all h (vs := [BitVec.ofNat 64 x0, BitVec.ofNat 64 x1,
    BitVec.ofNat 64 x2, BitVec.ofNat 64 x3]) (by
      simp only [List.mapM_cons, List.mapM_nil, readBits_b32 h0 (by omega),
        readBits_b32 h1 (by omega), readBits_b32 h2 (by omega), readBits_b32 h3 (by omega),
        bind, Except.bind, pure, Except.pure])
  have key : ∀ x : Nat, x < 2 ^ 31 → (BitVec.ofNat 32 (BitVec.ofNat 64 x).toNat).toInt = x := by
    intro x hx
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact toInt_ofNat_lt32 hx
  intro i
  rw [hv i]
  rcases i with ⟨_ | _ | _ | _ | i, hi⟩
  · exact key x0 hx0
  · exact key x1 hx1
  · exact key x2 hx2
  · exact key x3 hx3
  · simp [List.getD]

/-- A 32-bit register plus a zero offset, as a `.shared::cta` address. -/
theorem sharedEffAddr_b32 {L : Launch} {g : Nat} {t : TState} {r x : Nat}
    (hr : t.regs r = some (b32 x)) (hx : x < 2 ^ 32) :
    sharedEffAddr L g t false r 0 = .ok ⟨.shared, g / L.block, x⟩ := by
  have hv : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) + BitVec.ofInt 64 0)).toNat = x := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.ofInt_ofNat, BitVec.add_zero]
    omega
  simp only [sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind, pure, Except.pure,
    hv]

end

end PTX.Flow

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorBox
public import Lemmas.Flow.Store
public import Lemmas.Tensor.TensorMulticast

@[expose] public section

/-! # The origin of a tensor load or store

A proof tool. The origin of a tensor copy is read from the instruction's coordinate registers as a
signed 32-bit integer: its first coordinate is the low 32 bits of the first coordinate operand
(`fires_cpTensor_origin`, `fires_cpTensorStore_origin`). -/

namespace PTX.Flow

open PTX

/-- The first coordinate of a tensor load's origin is its first coordinate operand's low 32 bits. -/
theorem tensorLoadCopy_origin {L : Launch} {g : Nat} {t : TState} {ca grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {c0 : Opnd} {cs : List Opnd} {lm : TensorMode} {a : Nat}
    {s : TensorCopy.Spec}
    (h : tensorLoadCopy L g t ca grp dst off map (c0 :: cs) mb moff lm = .ok (a, s)) :
    ∃ bits, readBits L g t 32 c0 = .ok bits ∧
      s.origin 0 = (BitVec.ofNat 32 bits.toNat).toInt := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    List.mapM_cons] at h
  rcases hm : tensorMap L g t map (c0 :: cs) lm with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  dsimp only at h
  rcases hx : readBits L g t 32 c0 with f | x
  · simp only [hx] at h
    repeat' (split at h <;> (try (cases h)))
  · refine ⟨x, rfl, ?_⟩
    rcases hcs : cs.mapM (readBits L g t 32) with f | vs
    · simp only [hx, hcs] at h
      repeat' (split at h <;> (try (cases h)))
    · simp only [hx, hcs] at h
      repeat' (split at h <;> (try (cases h; done)))
      all_goals (cases h; try rfl)

/-- **A tensor load's origin.** -/
theorem fires_cpTensor_origin {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd} {c0 : Opnd} {cs : List Opnd}
    {lm : TensorMode} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor true grp dst off map (c0 :: cs) mb moff none lm)) e
      (some u)) :
    ∀ a s, e.kind = .tensorIssue a s → ∃ bits, readBits L g t 32 c0 = .ok bits ∧
      s.origin 0 = (BitVec.ofNat 32 bits.toNat).toInt := by
  intro a s hk
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor true grp dst off map (c0 :: cs) mb moff none lm))
      e (some u) := hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t) (ca := true) (grp := grp)
    (dst := dst) (mb := mb) (off := off) (moff := moff) (map := map) (cs := c0 :: cs) (lm :=
      lm) with
    ⟨f, hT⟩ | ⟨a', s', hT⟩
  · rw [hT] at hf'
    simp only [Fires] at hf'
    rw [hf'.1] at hk
    cases hk
  · rw [hT] at hf'
    obtain ⟨rfl, -⟩ := hf'
    obtain ⟨hcopy, -⟩ := tensorTmpl_unicast_issue hT
    simp only [Kind.tensorIssue.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact tensorLoadCopy_origin hcopy

/-- The first coordinate of a tensor store's origin is its first coordinate operand's low 32
bits. -/
theorem tensorStoreSpec_origin {L : Launch} {g : Nat} {t : TState} {map : Opnd} {c0 : Opnd}
    {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {a : Nat} {s : TensorStore.Spec}
    (h : tensorStoreSpec L g t map (c0 :: cs) src off policy mode reduce = .ok (a, s)) :
    ∃ bits, readBits L g t 32 c0 = .ok bits ∧
      s.origin 0 = (BitVec.ofNat 32 bits.toNat).toInt := by
  unfold tensorStoreSpec at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    List.mapM_cons] at h
  rcases hm : tensorMap L g t map (c0 :: cs) mode with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  dsimp only at h
  rcases hx : readBits L g t 32 c0 with f | x
  · simp only [hx] at h
    repeat' (split at h <;> (try (cases h)))
  · refine ⟨x, rfl, ?_⟩
    rcases hcs : cs.mapM (readBits L g t 32) with f | vs
    · simp only [hx, hcs] at h
      repeat' (split at h <;> (try (cases h)))
    · simp only [hx, hcs] at h
      repeat' (split at h <;> (try (cases h; done)))
      all_goals (cases h; try rfl)

/-- **A tensor store's origin.** -/
theorem fires_cpTensorStore_origin {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {map : Opnd} {c0 : Opnd} {cs : List Opnd} {src : Nat} {off : Int} {policy : Option Opnd}
    {mode : TensorMode} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map (c0 ::
      cs) src off policy mode reduce)) e o) :
    ∀ a s, e.kind = .tensorStore a s → ∃ bits, readBits L g t 32 c0 = .ok bits ∧
      s.origin 0 = (BitVec.ofNat 32 bits.toNat).toInt := by
  intro a s hk
  simp only [eventTmpl, tensorStoreTmpl] at hf
  cases hs : tensorStoreSpec L g t map (c0 :: cs) src off policy mode reduce with
  | error f =>
    simp only [hs, bind, Except.bind, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok r =>
    obtain ⟨a', s'⟩ := r
    simp only [hs, bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
    rw [hf.1] at hk
    simp only [Kind.tensorStore.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact tensorStoreSpec_origin hs

end PTX.Flow

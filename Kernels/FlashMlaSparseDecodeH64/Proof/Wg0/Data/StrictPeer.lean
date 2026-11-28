-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictLib
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Peer0

@[expose] public section

/-! # Conditions of the peer packs

A peer pack (`Gen.pk394` to `Gen.pk464`) widens four half words (`extE`), shifts two of them up
(`upperE`), merges them in pairs (`mergeE`) and packs the two pairs into a 128-bit word. With
every half word a `halfB` word (an `f32` or a 32-bit pattern) no step is a fault. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

noncomputable section

abbrev PkZ : Value := PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions.peerPackZero


/-- A half word of the peer pack. -/
def PkExt (x : Value) : Value := okVal (.bits 32 0) (extE [x])

/-- The shifted half word. -/
def PkUp (d : Nat) (s : List Nat) (x : Value) : Value :=
  okVal (.bits 32 0) (upperE d s [PkExt x])

theorem pkExt_eq {x : Value} (h : halfB x = true) : PkExt x = .pair x PkZ := by
  have e : extE [x] = .ok (Value.pair x PkZ) := by simp [extE, h]
  simp only [PkExt, e]; rfl

theorem pkUp_eq {d : Nat} {s : List Nat} {x : Value} (h : halfB x = true) :
    PkUp d s x = .pair PkZ x := by
  have e : upperE d s [.pair x PkZ] = .ok (Value.pair PkZ x) := by simp [upperE, h]
  simp only [PkUp, pkExt_eq h, e]; rfl

theorem c_ext {x : Value} (h : halfB x = true) : ∃ v, extE [x] = .ok v :=
  ⟨Value.pair x PkZ, by simp [extE, h]⟩

theorem c_up {d : Nat} {s : List Nat} {x : Value} (h : halfB x = true) :
    ∃ v, upperE d s [PkExt x] = .ok v :=
  ⟨Value.pair PkZ x, by simp [pkExt_eq h, upperE, h]⟩

theorem pkMlt {d : Nat} {s : List Nat} (hs : s.getD 0 0 < s.getD 1 0) {p q : Value}
    (hp : halfB p = true) (hq : halfB q = true) :
    okVal (.bits 32 0) (mergeE d s [PkUp d' s' p, PkExt q]) = .pair q p := by
  have hs' := hs
  simp only [List.getD_eq_getElem?_getD] at hs'
  simp [mergeE, pkUp_eq hp, pkExt_eq hq, hs', mergeOf, hp, hq, okVal]

theorem pkMge {d : Nat} {s : List Nat} (hs : ¬ s.getD 0 0 < s.getD 1 0) {p q : Value}
    (hp : halfB p = true) (hq : halfB q = true) :
    okVal (.bits 32 0) (mergeE d s [PkExt q, PkUp d' s' p]) = .pair q p := by
  have hs' := hs
  simp only [List.getD_eq_getElem?_getD] at hs'
  simp [mergeE, pkUp_eq hp, pkExt_eq hq, hs', mergeOf, hp, hq, okVal]

theorem halfB_bytes {v : Value} (h : halfB v = true) : v.bytes = 4 := by
  unfold halfB at h
  split at h <;> simp_all [Value.bytes]
  rfl

/-- The 128-bit pack of two pairs of half words. -/
theorem c_packPair {op : Op} {r1 r2 : Nat} {ty : DType} {d : Nat} {X Y a b c e : Value}
    (hop : op = .move ⟨.pack, ty, [some d], [.reg r1, .reg r2]⟩) (hty : ty.width = 128)
    (hne : r1 ≠ r2) (hX : X = .pair a b) (hY : Y = .pair c e) (ha : a.bytes = 4)
    (hb : b.bytes = 4) (hc : c.bytes = 4) (he : e.bytes = 4) :
    ∃ v, coreF op [r1, r2] [X, Y] = .ok v := by
  subst hop hX hY
  have h21 : (r2 == r1) = false := beq_false_of_ne (Ne.symm hne)
  simp [coreF, coreW, lk, oVal, ha, hb, hc, he, Value.bytes, List.lookup, hty, h21]
  exact ⟨_, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

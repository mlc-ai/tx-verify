-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.PtrRules

@[expose] public section

/-! # Addresses in closed form: the pointer runs on a generic shared pointer

The thread machine carries a generic shared pointer in an opaque slot and continues a pointer
run under the run's condition (each outcome is no fault). For the layers above, which know
the pointers, this file evaluates the pieces of the kernel's pointer runs, once:

* `ksax_eval`: `add.s64 p', base, k`, then the swizzle `shr.u64 x, p', 3`, `and.b64 y, x, 16`,
  `xor.b64 q, y, p'` (254 runs: the address of every carry load and of every final store but
  the first of each group);
* `r_eval`: `add.s64 p, base, word` (the base pointer `%rd4` of the carries, and the first
  instruction of 11 runs: the conversion loops and the first final store);
* `cvta_eval`: `cvta.shared.u64` of an integer, for a launched thread.

Where the base holds a generic shared pointer of offset `off` and each move stays in the
window (`MoveOk`, `MoveOkW`), the four or five outcomes are no fault, and the last one is the
pointer of the same window with the swizzled offset `swz (movedOff off k)`. The generated file
`RunPtr.lean` instantiates these for every pointer run of the kernel, as its condition and its
end facts. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread.Rules
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.FlashKdaFwd

/-- The offset of a pointer with offset `off` moved by the bits `delta` (read as a signed
64-bit integer), as `add.s64` computes it. -/
def movedBy (off delta : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((off.toNat : Int) + toSigned 64 (truncBits 64 delta))

/-- The offset of a pointer with offset `off` moved by the constant `k`. -/
abbrev movedOff (off : BitVec 64) (k : Int) : BitVec 64 := movedBy off (BitVec.ofInt 64 k)

/-- A pointer with offset `off` moved by the bits `delta` stays in the 32-bit window: the
condition under which `add.s64` on a shared pointer is no fault. -/
def MoveOkW (off delta : BitVec 64) : Prop :=
  off.toNat < 2 ^ 32 ∧ 0 ≤ (off.toNat : Int) + toSigned 64 (truncBits 64 delta) ∧
    (off.toNat : Int) + toSigned 64 (truncBits 64 delta) < 2 ^ 32

/-- The same for a constant `k`. -/
abbrev MoveOk (off : BitVec 64) (k : Int) : Prop := MoveOkW off (BitVec.ofInt 64 k)

/-- The swizzled offset: bit 4 is flipped when bit 7 is set. -/
def swz (off : BitVec 64) : BitVec 64 := off ^^^ ((off >>> 3) &&& 16#64)

/-- **A constant move and the swizzle on a generic shared pointer**: every outcome is no
fault, the moved pointer has the offset `movedOff off k`, and the last outcome is the pointer
with the swizzled offset. The terms are those a generated run has for `add.s64`,
`shr.u64 …, 3`, `and.b64 …, 16`, `xor.b64`. -/
theorem ksax_eval {k : Int} {vb : Value} {o c : Nat} {off : BitVec 64}
    (hb : vb = .ptr 64 true (.shared o c) off) (hk : MoveOk off k) :
    ((∃ v, add64KE k [vb] = .ok v) ∧
      (∃ v, swShrEK 3 [okVal (.bits 32 0) (add64KE k [vb])] = .ok v) ∧
      (∃ v, and64E 16 [okVal (.bits 32 0)
        (swShrEK 3 [okVal (.bits 32 0) (add64KE k [vb])])] = .ok v) ∧
      (∃ v, swXorE [okVal (.bits 32 0) (and64E 16 [okVal (.bits 32 0)
        (swShrEK 3 [okVal (.bits 32 0) (add64KE k [vb])])]),
          okVal (.bits 32 0) (add64KE k [vb])] = .ok v)) ∧
    okVal (.bits 32 0) (add64KE k [vb]) = .ptr 64 true (.shared o c) (movedOff off k) ∧
    okVal (.bits 32 0) (swXorE [okVal (.bits 32 0) (and64E 16 [okVal (.bits 32 0)
        (swShrEK 3 [okVal (.bits 32 0) (add64KE k [vb])])]),
          okVal (.bits 32 0) (add64KE k [vb])]) =
      .ptr 64 true (.shared o c) (swz (movedOff off k)) := by
  obtain ⟨h0, h1, h2⟩ := hk
  have a1 : add64KE k [vb] = .ok (.ptr 64 true (.shared o c) (movedOff off k)) := by
    rw [add64KE, hb, add64V_ptr h0 h1 h2]
    rfl
  have sw := swizzle_eval o c (movedOff off k)
  rw [okVal_of_ok a1]
  have a2 : swShrEK 3 [.ptr 64 true (.shared o c) (movedOff off k)] =
      .ok (.bits 64 (movedOff off k >>> 3)) := sw.1
  rw [okVal_of_ok a2]
  have a3 : and64E 16 [.bits 64 (movedOff off k >>> 3)] =
      .ok (.bits 64 ((movedOff off k >>> 3) &&& 16#64)) := sw.2.1
  rw [okVal_of_ok a3]
  have a4 : swXorE [.bits 64 ((movedOff off k >>> 3) &&& 16#64),
      .ptr 64 true (.shared o c) (movedOff off k)] =
        .ok (.ptr 64 true (.shared o c) (swz (movedOff off k))) := sw.2.2
  exact ⟨⟨⟨_, a1⟩, ⟨_, a2⟩, ⟨_, a3⟩, ⟨_, a4⟩⟩, rfl, okVal_of_ok a4⟩

/-- **A move by a word on a generic shared pointer**: the outcome of `add.s64 p, base, word`
where the base holds a generic shared pointer and the word register an integer. -/
theorem r_eval {vb vw : Value} {o c : Nat} {off delta : BitVec 64} {n : Nat}
    (hb : vb = .ptr 64 true (.shared o c) off) (hw : vw = .bits n delta)
    (hd : MoveOkW off delta) :
    add64E [vb, vw] = .ok (.ptr 64 true (.shared o c) (movedBy off delta)) := by
  obtain ⟨h0, h1, h2⟩ := hd
  rw [add64E, hb, hw, add64V_ptr h0 h1 h2]
  rfl

/-- **`cvta.shared.u64` of an integer, for a launched thread**: the condition of the piece
holds and it writes the generic pointer into the thread's own shared window at the integer's
offset. -/
theorem cvta_eval {L : Launch} {g : Nat} {V : Nat → Value} {a w : Nat} {x : BitVec 64}
    (hV : V a = .bits w x) (hg : g < L.threads) (hc : g / L.block < L.grid)
    (hx : (truncBits 64 x).toNat < 2 ^ 32) :
    cvtaCond L g V a ∧ cvtaVal L g V a =
      .ptr 64 true (.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (truncBits 64 x).toNat) := by
  have h : cvtaSharedE L g [V a] = .ok (.ptr 64 true (.shared (g / L.block) (g / L.block))
      (BitVec.ofNat 64 (truncBits 64 x).toNat)) := by
    rw [cvtaSharedE, hV, cvtaSharedV_bits hg hc hx]
  exact ⟨⟨_, h⟩, okVal_of_ok h⟩

/-- The bits of a natural number as an integer immediate. -/
theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- A constant that is a natural number below `2 ^ 63` is read as itself. -/
theorem toSigned_nat {k : Nat} (hk : k < 2 ^ 63) :
    toSigned 64 (truncBits 64 (BitVec.ofInt 64 (k : Int))) = (k : Int) := by
  rw [ofInt_natCast]
  simp only [toSigned, truncBits, BitVec.toNat_ofNat]
  split <;> omega

/-- **A constant that is a small natural number moves the offset by itself**: the form of the
kernel's 262 constant moves (all between 32768 and 97760). -/
theorem movedOff_nat {off : BitVec 64} {k : Nat} (hk : k < 2 ^ 63)
    (h : off.toNat + k < 2 ^ 32) :
    movedOff off (k : Int) = BitVec.ofNat 64 (off.toNat + k) ∧ MoveOk off (k : Int) := by
  have ht := toSigned_nat hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : ((off.toNat : Int) + (k : Int)) = ((off.toNat + k : Nat) : Int) := by omega
    rw [movedOff, movedBy, ht, e, ofInt_natCast]
  · omega
  · rw [ht]; omega
  · rw [ht]; omega

end PTX.Kernels.FlashKdaFwd.Proof.Thread.Rules

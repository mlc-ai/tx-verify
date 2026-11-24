-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Proof.NormRange
import Kernels.FlashKdaFwd.Audit.NormSums
import Lemmas.Flow.MaskedPack

/-! Widen every finite bfloat16 word into binary32, including signed zeros and subnormals. -/

namespace FlashKda.FiniteMask
open PTX OneToken Normalize

/-- A bfloat16 word is finite exactly when its eight exponent bits are not all ones.
The outer remainder in the decoder discards any bits above the 16-bit word. -/
def finiteWord (w : Nat) : Prop := w % 32768 / 128 ≠ 255

private theorem scale (m : ℚ) (e : ℤ) :
    m*65536*(2:ℚ)^(e-23) = m*2^(e-7) := by
  rw [show e-7 = 16+(e-23) by omega,zpow_add₀ (by norm_num)]
  norm_num
  ring

private theorem magnitude (f : Nat) :
    Layout.magnitude 8 23 (f*65536) = Layout.magnitude 8 7 f := by
  have e : f*65536/8388608 = f/128 := by omega
  have m : f*65536%8388608 = f%128*65536 := by omega
  have n : 8388608 + f%128*65536 = (128+f%128)*65536 := by omega
  unfold Layout.magnitude
  change (if f*65536/8388608 = 0 then _ else _) = (if f/128 = 0 then _ else _)
  rw [e]
  split
  · change ((f*65536%8388608 : Nat) : ℚ)*2^((1-Layout.bias 8)-23) = _
    rw [m,Nat.cast_mul]
    exact scale _ _
  · change ((8388608 + f*65536%8388608 : Nat) : ℚ) * 2^(((f*65536/8388608 : Nat):ℤ)
      -Layout.bias 8-23) = _
    rw [e,m,n,Nat.cast_mul]
    exact scale _ _

private theorem field (f : Nat) (s : Bool) :
    Layout.fieldVal 8 23 (f*65536) s = Layout.fieldVal 8 7 f s := by
  unfold Layout.fieldVal
  simp [magnitude]

/-- Value encoded by the sign, exponent and mantissa of a finite input word. -/
def datum (w : Nat) := Layout.fieldVal 8 7 (w%32768) (w%65536/32768%2 == 1)

private theorem decoded_word (w : Nat) (finite : finiteWord w) :
    brainFloat.decode w = some (datum w) ∧ binary32.decode (w <<< 16) = some (datum w) := by
  let f := w%32768
  let sign := w%65536/32768%2 == 1
  have short : w%65536%32768 = f := Nat.mod_mod_of_dvd w (by decide)
  have bits : w <<< 16 = w*65536 := Nat.shiftLeft_eq ..
  have long : (w*65536)%4294967296%2147483648 = f*65536 := by dsimp [f]; omega
  have exp : (f*65536)/8388608 = f/128 := by omega
  have neg : (w*65536)%4294967296/2147483648%2 = w%65536/32768%2 := by omega
  have low : brainFloat.decode w = some (Layout.fieldVal 8 7 f sign) := by
    change (if w%65536%32768/128 = 255 then _ else
      some (Layout.fieldVal 8 7 (w%65536%32768) sign)) = _
    rw [short,ite_eq_right finite]
  have high : binary32.decode (w <<< 16) = some (Layout.fieldVal 8 7 f sign) := by
    rw [bits]
    change (if (w*65536)%4294967296%2147483648/8388608 = 255 then _ else
      some (Layout.fieldVal 8 23 ((w*65536)%4294967296%2147483648)
        ((w*65536)%4294967296/2147483648%2 == 1))) = _
    rw [long,exp,ite_eq_right finite,neg,field]
  exact ⟨low,high⟩

/-- A finite input and its binary32 representation with sixteen appended zero bits
decode to the same finite datum. The check used by the normalization model always succeeds. -/
theorem widened_bits (w : Nat) (finite : finiteWord w) :
    ∃ x, brainFloat.decode w = some x ∧ widened w = some x ∧ NormRange.Finite x := by
  obtain ⟨low,high⟩ := decoded_word w finite
  refine ⟨_,low,by simp [widened,low,high,guard],?_⟩
  unfold datum Layout.fieldVal
  split <;> trivial

/-- Starting with the public 16 bits in a source register, the actual per-thread
conversion writes exactly the floating datum consumed by the modeled square updates. -/
theorem widen_register (L : Launch) (g : Nat) (t : TState) (src dst : Nat)
    (w : Fin 65536) (finite : finiteWord w)
    (read : t.regs src = some (.bits 16 (BitVec.ofNat 64 w))) :
    execLocal L g t (widen dst src).op = .ok (next (setReg t dst ((datum w).toValue .f32))) ∧
    widened w = some (datum w) := by
  obtain ⟨low,high⟩ := decoded_word w finite
  refine ⟨?_,by simp [widened,low,high,guard]⟩
  change execLocal L g t (.cvt (Flow.widenBfC dst (.reg src))) = _
  rw [Flow.execLocal_widenBf_core read]
  have cls := classify_bits (fmt := .bf16) (n := w) (by omega) low
  change classify .bf16 (.bits 16 (BitVec.ofNat 64 w)) = .ok (datum w) at cls
  unfold Flow.coreWidenBf
  rw [cls]
  let f := w.val%32768
  let sign := w.val%65536/32768%2 == 1
  have upper : Layout.magnitude 8 7 f ≤ binary32.maxNorm := by
    rw [← magnitude]
    apply (Layout.magnitude_strictMono 8 23).monotone
    change f*65536 ≤ 2139095039
    change w.val%32768/128 ≠ 255 at finite
    dsimp [f]
    omega
  have keep := Layout.magnitude_nonneg 8 7 f
  change (do
    let x ← widenElem (Flow.widenBfC 0 (.reg 0)) .f32 binary32 false (Layout.fieldVal 8 7 f sign)
    pure (x.toValue .f32) : Exec Value).map _ = _
  by_cases zero : f = 0
  · have val : datum w = .zero sign := by
      change Layout.fieldVal 8 7 f sign = _
      simp [Layout.fieldVal,zero]
    change (do
      let x ← widenElem _ _ _ _ (datum w)
      pure (x.toValue .f32) : Exec Value).map _ = _
    rw [val]
    rfl
  · let q := if sign then -Layout.magnitude 8 7 f else Layout.magnitude 8 7 f
    have val : datum w = .fin q := by
      change Layout.fieldVal 8 7 f sign = _
      simp [Layout.fieldVal,q,zero]
    have bounded : |q| ≤ binary32.maxNorm := by
      dsimp [q]
      split <;> simpa [abs_of_nonneg keep] using upper
    change (do
      let x ← widenElem _ _ _ _ (datum w)
      pure (x.toValue .f32) : Exec Value).map _ = _
    rw [val,widenElem_fin bounded]
    rfl

end FlashKda.FiniteMask

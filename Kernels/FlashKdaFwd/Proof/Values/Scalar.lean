-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Forms

@[expose] public section

/-!
# Form-level rules of the scalar instructions of a tile

Between the matrix instructions of a tile, every lane (one of the 32 threads of a warp) works on
single registers: it widens the raw bfloat16 inputs to binary32, evaluates the gate, computes
`(v - u) * beta`, narrows and packs accumulator registers, and updates the carried state with a
fused multiply-add. This file states each of these instructions in the vocabulary of
`Proof/Values/Forms.lean`, so that the generated register tables can be carried across them
without looking at machine values.

## The words used here

* `x : Inputs` holds the real arrays of the tile, `w` is the number of the warp and `l` the
  lane. A `Form` is the description the register table gives a data register, and
  `f.Holds x w l v` says that the value `v` is what the form `f` denotes in lane `l` of warp
  `w`.
* An *outcome function* maps the values of the source registers of one instruction to an
  `Exec Value`: `.ok u` when the instruction writes the value `u`, `.error …` when the thread
  faults there. The outcome functions of this kernel are those of `Proof/Thread/Rules.lean`
  (`Rules.shlKE`, `Rules.mulKE`, `Rules.addKE`, `Rules.rcpFE`, `Rules.zext16E`,
  `Rules.narrowE`, `Rules.pack32E`, `Rules.fmaE`) and of the library (`subE`, `mulE`, `ex2E`,
  `unpackE`).
* `okVal (.bits 32 0) E` is the value of the outcome `E`, and the 32-bit word zero where `E` is
  a fault. The generated run tables write the content of a destination register this way.
* The kernel's assumptions read a binary32 payload `.float .f32 y` as the real number `y`, and
  the floating instructions compute the exact real result on such numbers (the `_fin` lemmas of
  the outcome functions). So every rule below is an equation between real numbers, up to the
  position of the element in the lane's registers.
* Indices: `e` (0 or 1) selects the row `l / 4 + 8 * e` of the tile; `bi` (0 or 1) is the value
  block of the warp and `q` (0 or 1) the half of that block, eight value channels starting at
  `halfBase w bi q`; `r` is the index of a register in its group of four; `m` is a key block;
  `M : Mat` names a real matrix of the tile and `p` (0 or 1) a pair of accumulator registers.
  Accumulator register `r` of lane `l` holds the entry in row `cRow l r = l / 4 + 8 * (r / 2)`
  and column `cCol l r = 2 * (l % 4) + r % 2` of a 16 × 8 matrix.

## The rules

Every rule has the same two parts: the outcome function does not fault on values of the input
forms, and its value satisfies the output form.

| rule | instruction | input forms | output form |
| --- | --- | --- | --- |
| `shl_logit` | `shl.b32 …, 16` | `logitZ e` | `logitH e` |
| `mulK` | `mul.ftz.f32 …, 0fBFB8AA3B` | `logitH e` | `logitK e` |
| `ex2` | `ex2.approx.ftz.f32` | `logitK e` | `logitE e` |
| `addK` | `add.ftz.f32 …, 0f3F800000` | `logitE e` | `logitP e` |
| `rcp` | `rcp.approx.ftz.f32` | `logitP e` | `gate e` |
| `unpack` | `mov.b32 {lo, hi}, …` | `rawA bi r` | two `vRaw16 bi (r / 2) …` |
| `zext` | `cvt.u32.u16` | `vRaw16 bi q r` | `vBitsZ bi q r` |
| `shl_v` | `shl.b32 …, 16` | `vBitsZ bi q r` | `vBitsH bi q r` |
| `sub` | `sub.ftz.f32` | `vBitsH bi q r`, `regC (project kd bi q 8) r` | `diff bi q r` |
| `mul` | `mul.ftz.f32` | `gate (r / 2)`, `diff bi q r` | `regC (residual bi q) r` |
| `narrow` | `cvt.rn.bf16.f32` | `regC M r` | `narrowC M r` |
| `pack` | `mov.b32 …, {lo, hi}` | `narrowC M (2 p)`, `narrowC M (2 p + 1)` | `rowPair M p` |
| `fma` | `fma.rn.ftz.f32` | `carry m bi q r`, `decay m (r / 2)`, `regC (update bi q m) r` | … |

The output form of `fma` is `regC (nextState bi q m) r`. The constants `0fBFB8AA3B` and
`0f3F800000` are the 32-bit patterns `3216550459` and `1065353216` of the numbers
`Recurrence.multiplier` and `1` (`valFloat_gateMultiplier`, `valFloat_gateOne`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Fx
open PTX PTX.Proof PTX.Flow PTX.WarpMatrix PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.Kernels.FlashKdaFwd.Recurrence (multiplier)

noncomputable section

variable {x : Inputs} {w l : ℕ}

/-! ### The gate -/

/-- **`shl.b32 …, 16` of a gate logit.** The register holds the 32-bit word of a finite bfloat16
pattern, and a bfloat16 pattern is the upper half of the binary32 pattern of the same number
(`shlKE_16_word`), so the shifted word reads as the logit. -/
theorem shl_logit {e : ℕ} {v : Value} (h : (Form.logitZ e).Holds x w l v) :
    (∃ u, Rules.shlKE 16 [v] = .ok u) ∧
      (Form.logitH e).Holds x w l (okVal (.bits 32 0) (Rules.shlKE 16 [v])) := by
  simp only [Form.Holds] at h
  obtain ⟨n, hn, y, rfl, hy, hxy⟩ := h
  obtain ⟨z, hs, hb, hv⟩ := shlKE_16_word hn hy hxy
  exact ⟨⟨z, hs⟩, by rw [okVal_of_ok hs]; exact ⟨hb, hv⟩⟩

/-- **`mul.ftz.f32 …, 0fBFB8AA3B` of a gate logit.** The constant is the number
`Recurrence.multiplier`, and the product of two numbers is exact (`mulKE_gateMultiplier`). -/
theorem mulK {e : ℕ} {v : Value} (h : (Form.logitH e).Holds x w l v) :
    (∃ u, Rules.mulKE 3216550459 [v] = .ok u) ∧
      (Form.logitK e).Holds x w l (okVal (.bits 32 0) (Rules.mulKE 3216550459 [v])) := by
  have hE := mulKE_gateMultiplier h.2
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-- **`ex2.approx.ftz.f32` of the scaled logit.** The kernel's assumptions read the approximate
power of two of a number as the exact one (`ex2E_fin`). -/
theorem ex2 {e : ℕ} {v : Value} (h : (Form.logitK e).Holds x w l v) :
    (∃ u, ex2E true v = .ok u) ∧
      (Form.logitE e).Holds x w l (okVal (.bits 32 0) (ex2E true v)) := by
  have hv : v = .float .f32 (logitAt x l e * ((multiplier : ℚ) : ℝ)) := h
  have hE := ex2E_fin (fz := true) (va := v) (x := logitAt x l e * ((multiplier : ℚ) : ℝ))
    (by rw [hv]; rfl)
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-- **`add.ftz.f32 …, 0f3F800000` of the power of two.** The constant is the number `1`, and
the sum of two numbers is exact (`addKE_gateOne`). -/
theorem addK {e : ℕ} {v : Value} (h : (Form.logitE e).Holds x w l v) :
    (∃ u, Rules.addKE 1065353216 [v] = .ok u) ∧
      (Form.logitP e).Holds x w l (okVal (.bits 32 0) (Rules.addKE 1065353216 [v])) := by
  have hv : v = .float .f32 (Real.rpow 2 (logitAt x l e * ((multiplier : ℚ) : ℝ))) := h
  have hE := addKE_gateOne (va := v)
    (x := Real.rpow 2 (logitAt x l e * ((multiplier : ℚ) : ℝ))) (by rw [hv]; rfl)
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-- **`rcp.approx.ftz.f32` of the denominator of the gate.** The operand is `2 ^ y + 1`, which
is positive (`gate_ne_zero`), so the reciprocal does not fault, and the assumptions read it as
the exact reciprocal (`Rules.rcpFE_fin`): the gate strength of the row, `Math.Fragments.gate`. -/
theorem rcp {e : ℕ} {v : Value} (h : (Form.logitP e).Holds x w l v) :
    (∃ u, Rules.rcpFE [v] = .ok u) ∧
      (Form.gate e).Holds x w l (okVal (.bits 32 0) (Rules.rcpFE [v])) := by
  have hv : v = .float .f32 (Real.rpow 2 (logitAt x l e * ((multiplier : ℚ) : ℝ)) + 1) := h
  have hE := Rules.rcpFE_fin (va := v)
    (x := Real.rpow 2 (logitAt x l e * ((multiplier : ℚ) : ℝ)) + 1) (by rw [hv]; rfl)
    (gate_ne_zero _)
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-! ### The values `v` and the residual -/

-- The bounds `hl` and `hr` are the ranges in which the register table uses this rule; the index
-- identity holds for all lanes and registers, so the proof does not read them.
set_option linter.unusedVariables false in
/-- **`mov.b32 {lo, hi}, r` of a register of the block of `v`.** The block of `v` is loaded in
the layout of an A operand; half `i` of its register `r` is the element that accumulator
register `2 * (r % 2) + i` of the half `r / 2` of the value block holds (`aRow_cRow`,
`aCol_cCol` and `halfBase_add` of `Math/FragmentsLayout.lean`). The split itself is
`RawPair.unpack` and `RawPair.split`. -/
theorem unpack {bi r q r' : ℕ} {v : Value} (hl : l < 32) (hr : r < 4) (hq : q = r / 2)
    (hr' : r' = 2 * (r % 2)) (h : (Form.rawA bi r).Holds x w l v) :
    (∃ p, unpackE 32 v = .ok p) ∧ (Form.vRaw16 bi q r').Holds x w l (splitValue 32 v).1 ∧
      (Form.vRaw16 bi q (r' + 1)).Holds x w l (splitValue 32 v).2 := by
  subst hq hr'
  have hix : ∀ i < 2, x.value (aRow l r) (halfBase w bi 0 + aCol l r i) =
      vAt x w l bi (r / 2) (2 * (r % 2) + i) := fun i hi => by
    rw [vAt, ← aRow_cRow l r hi, ← halfBase_add w bi (r / 2), aCol_cCol l r hi]
    congr 1
    omega
  have hp : RawPair v (vAt x w l bi (r / 2) (2 * (r % 2) + 0))
      (vAt x w l bi (r / 2) (2 * (r % 2) + 1)) := by
    rw [← hix 0 (by omega), ← hix 1 (by omega)]; exact h
  exact ⟨⟨_, hp.unpack⟩, hp.split⟩

/-- **`cvt.u32.u16` of an element of `v`.** The 16 bits of the register are a finite bfloat16
pattern, and the zero-extension writes the 32-bit word of that pattern (`Bf16Of.zext16`). -/
theorem zext {bi q r : ℕ} {v : Value} (h : (Form.vRaw16 bi q r).Holds x w l v) :
    (∃ u, Rules.zext16E [v] = .ok u) ∧
      (Form.vBitsZ bi q r).Holds x w l (okVal (.bits 32 0) (Rules.zext16E [v])) := by
  obtain ⟨n, hn, y, hz, hy, hxy⟩ := Bf16Of.zext16 (show Bf16Of v (vAt x w l bi q r) from h)
  exact ⟨⟨_, hz⟩, by rw [okVal_of_ok hz]; exact ⟨n, hn, y, rfl, hy, hxy⟩⟩

/-- **`shl.b32 …, 16` of an element of `v`.** As for the gate logit (`shl_logit`): the shifted
word of a finite bfloat16 pattern reads as the binary32 number of the pattern. -/
theorem shl_v {bi q r : ℕ} {v : Value} (h : (Form.vBitsZ bi q r).Holds x w l v) :
    (∃ u, Rules.shlKE 16 [v] = .ok u) ∧
      (Form.vBitsH bi q r).Holds x w l (okVal (.bits 32 0) (Rules.shlKE 16 [v])) := by
  simp only [Form.Holds] at h
  obtain ⟨n, hn, y, rfl, hy, hxy⟩ := h
  obtain ⟨z, hs, hb, hv⟩ := shlKE_16_word hn hy hxy
  exact ⟨⟨z, hs⟩, by rw [okVal_of_ok hs]; exact ⟨hb, hv⟩⟩

/-- **`sub.ftz.f32`: `v - u`.** The first operand reads as the element of `v`, the second is the
accumulator `u = k_decayed · S` after its eight key blocks at the same position, and the
difference of two numbers is exact (`subE_fin`). -/
theorem sub {bi q r : ℕ} {a b : Value} (ha : (Form.vBitsH bi q r).Holds x w l a)
    (hb : (Form.regC (.project .kd bi q 8) r).Holds x w l b) :
    (∃ u, subE true a b = .ok u) ∧
      (Form.diff bi q r).Holds x w l (okVal (.bits 32 0) (subE true a b)) := by
  have hb' : b = .float .f32
      (project x.decayedKey x.copy (halfBase w bi q) 8 (cRow l r) (cCol l r)) := hb
  have hE := subE_fin (fz := true) (vb := b)
    (y := project x.decayedKey x.copy (halfBase w bi q) 8 (cRow l r) (cCol l r)) ha.2
    (by rw [hb']; rfl)
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-- **`mul.ftz.f32`: `beta * (v - u)`.** Accumulator register `r` holds an entry of the row
`l / 4 + 8 * (r / 2)`, so its gate is the one of `e = r / 2`; the product of two numbers is
exact (`mulE_fin`) and is the entry of `Math.Fragments.residual`. -/
theorem mul {bi q r e : ℕ} {a b : Value} (he : e = r / 2) (ha : (Form.gate e).Holds x w l a)
    (hb : (Form.diff bi q r).Holds x w l b) :
    (∃ u, mulE true a b = .ok u) ∧
      (Form.regC (.residual bi q) r).Holds x w l (okVal (.bits 32 0) (mulE true a b)) := by
  subst he
  have ha' : a = .float .f32 (gate x (l / 4 + 8 * (r / 2))) := ha
  have hb' : b = .float .f32 (vAt x w l bi q r -
      project x.decayedKey x.copy (halfBase w bi q) 8 (cRow l r) (cCol l r)) := hb
  have hE := mulE_fin (fz := true) (va := a) (vb := b) (x := gate x (l / 4 + 8 * (r / 2)))
    (y := vAt x w l bi q r -
      project x.decayedKey x.copy (halfBase w bi q) 8 (cRow l r) (cCol l r))
    (by rw [ha']; rfl) (by rw [hb']; rfl)
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-! ### Narrowing, packing and the state update -/

/-- **`cvt.rn.bf16.f32` of an accumulator register.** The kernel rule `narrow` reads the
conversion of a number as the bfloat16 payload of the same number (`Rules.narrowE_fin`). -/
theorem narrow {M : Mat} {r : ℕ} {v : Value} (h : (Form.regC M r).Holds x w l v) :
    (∃ u, Rules.narrowE [v] = .ok u) ∧
      (Form.narrowC M r).Holds x w l (okVal (.bits 32 0) (Rules.narrowE [v])) := by
  have hv : v = .float .f32 (M.eval x w (cRow l r) (cCol l r)) := h
  have hE := Rules.narrowE_fin (v := v) (x := M.eval x w (cRow l r) (cCol l r))
    (by rw [hv]; rfl)
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-- **`mov.b32 d, {lo, hi}` of two narrowed accumulator registers.** Two bfloat16 payloads have
two bytes each, so the pack succeeds with their pair (`Rules.pack32E_bf16`), which is the
content `Math.Fragments.rowPair` describes for the registers `2 * p` and `2 * p + 1`. -/
theorem pack {M : Mat} {p : ℕ} {a b : Value} (ha : (Form.narrowC M (2 * p)).Holds x w l a)
    (hb : (Form.narrowC M (2 * p + 1)).Holds x w l b) :
    (∃ u, Rules.pack32E [a, b] = .ok u) ∧
      (Form.rowPair M p).Holds x w l (okVal (.bits 32 0) (Rules.pack32E [a, b])) := by
  have ha' : a = .float .bf16 (M.eval x w (cRow l (2 * p)) (cCol l (2 * p))) := ha
  have hb' : b = .float .bf16 (M.eval x w (cRow l (2 * p + 1)) (cCol l (2 * p + 1))) := hb
  subst ha' hb'
  have hE := Rules.pack32E_bf16 (M.eval x w (cRow l (2 * p)) (cCol l (2 * p)))
    (M.eval x w (cRow l (2 * p + 1)) (cCol l (2 * p + 1)))
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

/-- **`fma.rn.ftz.f32`: `carry * g_total + acc`.** Accumulator register `r` holds an entry of
the row `l / 4 + 8 * (r / 2)`, so the decay of key feature `16 * m + l / 4 + 8 * e` with
`e = r / 2` is the one of the carry's key feature `16 * m + cRow l r`; the fused multiply-add of
three numbers is exact (`Rules.fmaE_fin`) and is the entry of `Math.Fragments.nextState`. -/
theorem fma {m bi q r e : ℕ} {a b c : Value} (he : e = r / 2)
    (ha : (Form.carry m bi q r).Holds x w l a) (hb : (Form.decay m e).Holds x w l b)
    (hc : (Form.regC (.update bi q m) r).Holds x w l c) :
    (∃ u, Rules.fmaE [a, b, c] = .ok u) ∧
      (Form.regC (.nextState bi q m) r).Holds x w l
        (okVal (.bits 32 0) (Rules.fmaE [a, b, c])) := by
  subst he
  have hrow : 16 * m + l / 4 + 8 * (r / 2) = 16 * m + cRow l r := by unfold cRow; omega
  have ha' : a = .float .f32 (x.carry (16 * m + cRow l r) (halfBase w bi q + cCol l r)) := ha
  have hb' : b = .float .f32 (x.totalDecay (16 * m + cRow l r)) := by rw [← hrow]; exact hb
  have hc' : c = .float .f32 (update x (halfBase w bi q) m (cRow l r) (cCol l r)) := hc
  have hE := Rules.fmaE_fin (va := a) (vb := b) (vc := c)
    (x := x.carry (16 * m + cRow l r) (halfBase w bi q + cCol l r))
    (y := x.totalDecay (16 * m + cRow l r))
    (z := update x (halfBase w bi q) m (cRow l r) (cCol l r))
    (by rw [ha']; rfl) (by rw [hb']; rfl) (by rw [hc']; rfl)
  exact ⟨⟨_, hE⟩, by rw [okVal_of_ok hE]; rfl⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Fx

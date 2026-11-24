-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assembly.Correctness
public import Kernels.RmsNorm.Ptx
public import Kernels.RmsNorm.Data.Decoded
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# `rmsnorm`: what is proved (read this file and `Theorem.lean`)

The launch data, the precondition on the launch and the memory at launch, and the
postcondition. The kernel is `kernel`, the decoding of `rmsnorm.ptx`
(`decode_eq`).
-/

namespace PTX.Kernels.RmsNorm
open PTX Finset

/-- The decoded program of `rmsnorm.ptx`; `decode_eq` checks that the source decodes to it. -/
def kernel : Kernel := Decoded.kernel

set_option maxRecDepth 100000 in
theorem decode_eq :
    Decode.kernelIn Generated.RmsNorm.module.globals Generated.RmsNorm.rmsnorm_kernel =
      .ok kernel := by
  rfl

theorem code_len : kernel.code.length = 295 := Decoded.code_length
theorem code_none (pc : Nat) (h : 295 ≤ pc) : kernel.code[pc]? = none := by
  simp [code_len, h]


def gl (a : Nat) : Loc := ⟨.global, 0, a⟩
def h16 (x : ℝ) : Value := .float .f16 x


/-- Launch data: input `I`, output `O`, weight `W` (byte addresses), batch `Bt`, shared
window base `S`; input row-major `x`, weight `w`. -/
structure Params where
  I : Nat
  O : Nat
  W : Nat
  Bt : Nat
  S : Nat
  x : Nat → ℝ
  w : Nat → ℝ

/-- Element `k` of row `r`. -/
def xe (P : Params) (r k : Nat) : ℝ := P.x (4096 * r + k)

/-- Launch shape, parameters and address bounds (part of the precondition). -/
structure Hyp (P : Params) (L : Launch) : Prop where
  grid : L.grid = 152
  block : L.block = 256
  shared : L.sharedBase = P.S
  param0 : L.params "rmsnorm_kernel_param_0" = some (BitVec.ofNat 64 P.I)
  param1 : L.params "rmsnorm_kernel_param_1" = some (BitVec.ofNat 64 P.O)
  param2 : L.params "rmsnorm_kernel_param_2" = some (BitVec.ofNat 64 P.W)
  param3 : L.params "rmsnorm_kernel_param_3" = some (BitVec.ofNat 64 P.Bt)
  batch : P.Bt + 152 ≤ 2 ^ 20
  sharedEnd : P.S + 16416 ≤ 2 ^ 32
  sharedAlign : P.S % 16 = 0
  inEnd : P.I + 8192 * P.Bt < 2 ^ 64
  outEnd : P.O + 8192 * P.Bt < 2 ^ 64
  wEnd : P.W + 8192 < 2 ^ 64
  inAlign : P.I % 16 = 0
  outAlign : P.O % 16 = 0
  wAlign : P.W % 16 = 0
  /-- The grid consists of whole clusters, as required by the launch model. -/
  oneDimLaunch : L.oneDimLaunch

def InI (P : Params) (l : Loc) : Prop :=
    l.space = .global ∧ l.cta = 0 ∧ P.I ≤ l.addr ∧ l.addr < P.I + 8192 * P.Bt
def InW (P : Params) (l : Loc) : Prop :=
    l.space = .global ∧ l.cta = 0 ∧ P.W ≤ l.addr ∧ l.addr < P.W + 8192
def InO (P : Params) (l : Loc) : Prop :=
    l.space = .global ∧ l.cta = 0 ∧ P.O ≤ l.addr ∧ l.addr < P.O + 8192 * P.Bt
def InS (P : Params) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta < 152 ∧ l.cta < P.Bt ∧ P.S ≤ l.addr ∧ l.addr < P.S + 16416


noncomputable section

/-- Precondition: launch shape, parameters, and the memory at launch. -/
structure Pre (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  hyp : Hyp P L
  disjIO : P.I + 8192 * P.Bt ≤ P.O ∨ P.O + 8192 * P.Bt ≤ P.I
  disjWO : P.W + 8192 ≤ P.O ∨ P.O + 8192 * P.Bt ≤ P.W
  disjIW : P.I + 8192 * P.Bt ≤ P.W ∨ P.W + 8192 ≤ P.I
  input : ∀ a < 8192 * P.Bt, mem0 (gl (P.I + a)) = some (some (h16 (P.x (a / 2)), a % 2))
  weight : ∀ a < 8192, mem0 (gl (P.W + a)) = some (some (h16 (P.w (a / 2)), a % 2))
  output : ∀ a < 8192 * P.Bt, mem0 (gl (P.O + a)) ≠ none
  shared : ∀ c < 152, c < P.Bt → ∀ a < 16416,
    mem0 ⟨.shared, c, P.S + a⟩ ≠ none

/-- `eps`: the binary32 literal `0x358637BD` (about `1e-6`) as a real. -/
noncomputable def eps : ℝ := (((f32Value 897988541).getD 0 : ℚ) : ℝ)

/-- The specification: element `k` of output row `r`. -/
noncomputable def y (P : Params) (r k : Nat) : ℝ :=
  xe P r k * (1 / Real.sqrt ((∑ k' ∈ range 4096, xe P r k' ^ 2) / 4096 + eps)) * P.w k

/-- Element `k` of output row `r`, read as `f16` (`memFloat`: the bytes as `ld` rebuilds them,
read as an `f16` operand), is `y P r k`; all other global memory is unchanged. -/
def Post (P : Params) (mem0 : Mem0) (m : FinalMem) : Prop :=
  (∀ r < P.Bt, ∀ k < 4096, memFloat .f16 m (gl (P.O + 2 * (4096 * r + k))) = .ok (y P r k)) ∧
  (∀ l : Loc, l.space = .global → ¬ InO P l → m l = mem0 l)

end

end PTX.Kernels.RmsNorm

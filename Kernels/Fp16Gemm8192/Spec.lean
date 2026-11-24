-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Kernels.Fp16Gemm8192.Data.TensorMaps
public import Kernels.Fp16Gemm8192.Data.Decoded

@[expose] public section

/-!
The production FP16 GEMM on 8192-square operands, with input empty-barrier tail drain.

The host stores A as M x K and B as N x K, so the mathematical result is A * Bᵀ.
Floating values denote exact reals under the explicitly selected `idealReal` profile.
The precondition describes launch bindings, input bytes and available storage/resources.
Task coverage, buffer ownership, synchronization and progress are proof obligations.
-/

namespace PTX.Kernels.Fp16Gemm8192
open PTX
noncomputable section

/-- All 1097 decoded instructions of the frozen production program. -/
def kernel : Kernel := Decoded.kernel

theorem kernel_code_length : kernel.code.length = 1097 := Decoded.code_length

theorem kernel_groupUniform : kernel.TcGroupUniform := by
  unfold Kernel.TcGroupUniform
  decide +kernel

/-- Bytes in each contiguous 8192 x 8192 FP16 matrix. -/
def matrixBytes : Nat := 134217728

/-- The production shared pool: 1 KiB of control storage, four input stages,
and two epilogue buffers for each of the two consumer groups. -/
def sharedBytes : Nat := 230400

structure Params where
  aBase : Nat
  bBase : Nat
  dBase : Nat
  aMap : Nat
  bMap : Nat
  dMap : Nat
  aClass : TensorDescriptor.AllocationClass
  bClass : TensorDescriptor.AllocationClass
  dClass : TensorDescriptor.AllocationClass
  a : Nat → Nat → ℝ
  b : Nat → Nat → ℝ

/-- The actual by-value tensor-map parameter declaration in the compiled PTX. -/
def mapParam (name : String) : ParamObjectDecl := ⟨name, 8, 128, 128⟩

theorem kernel_paramObjects : kernel.paramObjects =
    [mapParam "gemm_kernel_param_0", mapParam "gemm_kernel_param_1",
      mapParam "gemm_kernel_param_2"] := rfl

/-- Row-major FP16 element address; its two byte addresses are `at 0` and `at 1`. -/
def elementLoc (base row col : Nat) : Loc :=
  ⟨.global, 0, base + 2 * (8192 * row + col)⟩

/-- The first `n` terms of the ideal dot product. -/
def prefixDot (P : Params) (row col n : Nat) : ℝ :=
  ∑ k ∈ Finset.range n, P.a row k * P.b col k

def dot (P : Params) (row col : Nat) : ℝ := prefixDot P row col 8192

/-- Initial launch and memory requirements, without execution or protocol assumptions. -/
structure Pre (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  grid : L.grid = 1024
  block : L.block = 384
  cluster : L.clusterSize.val = 2
  /-- The launch is one-dimensional: a one-dimensional grid made of whole one-dimensional
  clusters. -/
  oneDimLaunch : L.oneDimLaunch
  paramA : L.paramObjects "gemm_kernel_param_0" =
    some (mapParam "gemm_kernel_param_0", P.aMap)
  paramB : L.paramObjects "gemm_kernel_param_1" =
    some (mapParam "gemm_kernel_param_1", P.bMap)
  paramD : L.paramObjects "gemm_kernel_param_2" =
    some (mapParam "gemm_kernel_param_2", P.dMap)
  mapA : L.tensorMaps P.aMap = some ⟨1, Fp16Gemm8192.mapA P.aBase P.aClass⟩
  mapB : L.tensorMaps P.bMap = some ⟨1, Fp16Gemm8192.mapB P.bBase P.bClass⟩
  mapD : L.tensorMaps P.dMap = some ⟨1, Fp16Gemm8192.mapD P.dBase P.dClass⟩
  mapAlignment : P.aMap % 128 = 0 ∧ P.bMap % 128 = 0 ∧ P.dMap % 128 = 0
  mapRange : P.aMap + 128 ≤ 2 ^ 64 ∧ P.bMap + 128 ≤ 2 ^ 64 ∧
    P.dMap + 128 ≤ 2 ^ 64
  mapDisjointAB : P.aMap + 128 ≤ P.bMap ∨ P.bMap + 128 ≤ P.aMap
  mapDisjointAD : P.aMap + 128 ≤ P.dMap ∨ P.dMap + 128 ≤ P.aMap
  mapDisjointBD : P.bMap + 128 ≤ P.dMap ∨ P.dMap + 128 ≤ P.bMap
  inputAlignment : P.aBase % 16 = 0 ∧ P.bBase % 16 = 0 ∧ P.dBase % 16 = 0
  matrixRange : P.aBase + matrixBytes ≤ 2 ^ 64 ∧
    P.bBase + matrixBytes ≤ 2 ^ 64 ∧ P.dBase + matrixBytes ≤ 2 ^ 64
  outputDisjointA : P.aBase + matrixBytes ≤ P.dBase ∨ P.dBase + matrixBytes ≤ P.aBase
  outputDisjointB : P.bBase + matrixBytes ≤ P.dBase ∨ P.dBase + matrixBytes ≤ P.bBase
  inputA : ∀ row < 8192, ∀ k < 8192, ∀ byte < 2,
    mem0 ((elementLoc P.aBase row k).at byte) =
      some (some ((Value.float .f16 (P.a row k)).byteAt byte))
  inputB : ∀ col < 8192, ∀ k < 8192, ∀ byte < 2,
    mem0 ((elementLoc P.bBase col k).at byte) =
      some (some ((Value.float .f16 (P.b col k)).byteAt byte))
  outputAllocated : ∀ byte < matrixBytes,
    mem0 ⟨.global, 0, P.dBase + byte⟩ ≠ none
  sharedAlignment : L.sharedBase % 1024 = 0
  sharedRange : L.sharedBase + sharedBytes ≤ 2 ^ 18
  sharedAllocated : ∀ cta < L.grid, ∀ byte < sharedBytes,
    mem0 ⟨.shared, cta, L.sharedBase + byte⟩ ≠ none

/-- Complete ideal GEMM output: element `(row, col)` of `D`, read as `f16` (`memFloat`: the
bytes as `ld` rebuilds them, read as an `f16` operand), is the ideal dot product; every other
global byte is preserved. Output contents at launch are unconstrained. Each task's first MMA must
establish a fresh accumulator. -/
def Post (P : Params) (mem0 : Mem0) (m : FinalMem) : Prop :=
  (∀ row < 8192, ∀ col < 8192,
    memFloat .f16 m (elementLoc P.dBase row col) = .ok (dot P row col)) ∧
  ∀ l, l.space = .global →
    ¬ (l.cta = 0 ∧ P.dBase ≤ l.addr ∧ l.addr < P.dBase + matrixBytes) → m l = mem0 l

end
end PTX.Kernels.Fp16Gemm8192

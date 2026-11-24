-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # The kernel's global memory accesses

Every access of a global byte is a tensor load reading the `A` or `B` matrix or a tensor store
writing the `D` matrix (`global_access`): a thread reads and writes only shared memory
(`ThreadFacts.access_region`, `write_shared`), and every other asynchronous access is to shared
memory. A tensor load reads through the `A` or `B` map (`ThreadFacts.tensor_issue`), a tensor store
writes through the `D` map (`ThreadFacts.store_map`), and a map's element addresses lie in its
matrix (`lookup_in`). So two conflicting accesses of a global byte are two output writes, which the
output tiles keep apart (`OutputUnique`), or an output write and an input read, which `Pre` keeps
apart (`global_ordered`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory

open PTX AsyncCopy TensorDescriptor

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A byte of the global matrix at `base`. -/
def InMatrix (base : Nat) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧ base ≤ l.addr ∧ l.addr < base + matrixBytes

/-- An element address of an `8192 x 8192` FP16 map lies in its matrix. -/
theorem lookup_in {base bi bo : Nat} {sw : TensorSwizzle.Mode} {cls : AllocationClass}
    {c : Fin 2 → Int} {byte addr : Nat}
    (h : TensorAddress.lookup (geometry (encodeTiled .f16 base 8192 8192 16384 bi bo sw cls)) c
      byte = some addr) : base ≤ addr ∧ addr < base + matrixBytes := by
  obtain ⟨hin, hb, rfl⟩ := (TensorAddress.lookup_some_iff _ _ _ _).mp h
  have h0 := hin 0
  have h1 := hin 1
  simp only [geometry, encodeTiled, Format.bytes, Fin.val_zero, Fin.val_one, ite_true,
    show (1 : Nat) ≠ 0 by decide, ite_false, Nat.cast_ofNat] at h0 h1 hb
  simp only [TensorAddress.byteAddress, Fin.sum_univ_succ, Fin.sum_univ_zero, geometry,
    encodeTiled, Format.bytes, Fin.cases_zero, Fin.cases_succ]
  have h1' : 0 ≤ c (Fin.succ 0) ∧ c (Fin.succ 0) < 8192 := h1
  unfold matrixBytes
  omega

/-- A store through the `D` map writes the `D` matrix. -/
theorem store_in {b : Nat} {cls : AllocationClass} {s : TensorStore.Spec}
    (hd : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) = ⟨1, Fp16Gemm8192.mapD b cls⟩)
    {x y k : Nat} {l : Loc} (h : TensorStore.writeLoc s x y k = some l) : InMatrix b l := by
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := s
  simp only [Sigma.mk.injEq] at hd
  obtain ⟨rfl, hdesc⟩ := hd
  cases hdesc
  simp only [TensorStore.writeLoc, TensorStore.destination, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at h
  obtain ⟨slot, -, addr, ha, rfl⟩ := h
  obtain ⟨h1, h2⟩ := lookup_in ha
  exact ⟨rfl, rfl, h1, h2⟩

/-- A load of a stage through an operand map reads the map's matrix. -/
theorem copy_in {b : Nat} {cls : AllocationClass} {origin : Fin 2 → Int} {cta stage : Nat}
    {mbar : Loc} {ca : Bool} {grp : CtaGroup} {x y k : Nat} {l : Loc}
    (h : TensorCopy.readLoc (stageCopy (Fp16Gemm8192.mapA b cls) origin cta stage mbar ca grp)
      x y k = some l) : InMatrix b l := by
  rw [TensorCopy.readLoc_source] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨slot, -, hs⟩ := h
  unfold TensorCopy.source at hs
  rcases hga : (stageCopy (Fp16Gemm8192.mapA b cls) origin cta stage mbar ca grp).globalAddress
    slot with _ | addr
  · simp only [hga] at hs
    cases hs
  · simp only [hga, Option.some.injEq] at hs
    subst hs
    obtain ⟨h1, h2⟩ := lookup_in hga
    exact ⟨rfl, rfl, h1, h2⟩

end PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory

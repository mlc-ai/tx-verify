-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Index
public import Lemmas.Flow.SignedBits

@[expose] public section

/-! # The index role's launch test follows from the launch preconditions

`Wg1Index.LaunchTest` states that the two optional length pointers' 64-bit words are null exactly
when the parameter has no runtime length, and that the signed batch test is false for a CTA of the
grid. Both follow from `Pre`: the pointer bytes, the non-null and 64-bit bounds of the bound
values, and the grid's `(s_q, b, 1)` block indices. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Interface
open PTX

noncomputable section

/-- The linear block index of a thread. -/
def ctaOf (L : Launch) (g : Nat) : Nat := g / L.block

/-- `%ctaid.y` of the thread's CTA: the batch of the kernel's `(s_q, b, 1)` grid. -/
def batchOf (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).y % 2 ^ 32

theorem batchOf_eq_ctaidY (L : Launch) (g : Nat) : batchOf L g = ctaidY L g := rfl

/-- The CTAs of the kernel's grid are the launch's `(s_q, b, 1)` block indices. -/
theorem ctaidOf_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (c : Nat) :
    L.ctaidOf c = ⟨c % P.s_q, c / P.s_q % P.b, 0⟩ := by
  have hsz : L.clusterSize.val = 1 := hpre.clusterSize
  have hloc : ∀ (n k cc : Nat), L.locate n k cc = (k + cc, 0) := by
    intro n k cc
    rw [Launch.locate_regular (fun k => by rw [hpre.clusterPlaces, hsz]; rfl), hsz,
      Nat.div_one, Nat.mod_one]
  have hco : L.clusterOfCta c = c := by
    simp only [Launch.clusterOfCta, hloc, Nat.zero_add]
  have hrk : L.rankOfCta c = 0 := by
    simp only [Launch.rankOfCta, hloc]
  have hplace : L.clusterPlaces c = ⟨⟨c % P.s_q, c / P.s_q % P.b, 0⟩, ⟨1, 1, 1⟩,
      ⟨c % P.s_q, c / P.s_q % P.b, 0⟩, ⟨P.s_q, P.b, 1⟩⟩ := by
    rw [hpre.clusterPlaces]
    rfl
  simp only [Launch.ctaidOf, Launch.placeOf, hco, hplace, Launch.clusterCtaidOf, hrk,
    Dim3.coord]
  simp only [Nat.mod_one, Nat.div_one, Nat.zero_add, Nat.add_zero]

/-- The batch of the thread's CTA, as the linear block index gives it. -/
theorem batchOf_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (g : Nat) :
    batchOf L g = (g / L.block) / P.s_q % P.b := by
  unfold batchOf ctaOf
  rw [ctaidOf_eq hpre]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpre.bPos) hpre.bRange)

/-- The thread's CTA is a batch index of the grid. -/
theorem batchOf_lt (P : Params) (L : Launch) (mem0 : Mem0) (hpre : Pre P L mem0) (g : Nat) :
    batchOf L g < P.b := by
  rw [batchOf_eq hpre]
  exact Nat.mod_lt _ hpre.bPos

/-- A `geq` comparison of two nonnegative signed 32-bit words below `2 ^ 31` is false when the
left is smaller. -/
theorem compare_ge_s32_false {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h : a < b) :
    compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = false := by
  norm_signed

/-- The batch test `setp.ge.s32 %p, %ctaid.y, b` is false for a CTA of the grid. -/
theorem geBatch_false {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    Thread.geBatch L g = false := by
  have h := batchOf_lt P L mem0 hpre g
  have hb32 : P.b % 2 ^ 32 = P.b := Nat.mod_eq_of_lt (by have := hpre.bLt; omega)
  have ha : batchOf L g < 2 ^ 31 := lt_trans h hpre.bLt
  unfold Thread.geBatch
  rw [show Thread.ctaidY L g = batchOf L g from rfl, Thread.paramWord_b hpre, hb32]
  exact compare_ge_s32_false ha hpre.bLt h

/-- The main-cache length word is null exactly when the parameter has no runtime length. -/
theorem ptrIsNull_80 (P : Params) (L : Launch) (mem0 : Mem0) (hpre : Pre P L mem0) :
    Thread.ptrIsNull L 80 = !P.topkLenBase.isSome := by
  cases h : P.topkLenBase with
  | none =>
    rw [Thread.ptrIsNull, Thread.paramWord_80_zero hpre h]
    rfl
  | some x =>
    rw [Thread.ptrIsNull, Thread.paramWord_80_some hpre h]
    have hlt := hpre.topkLenBaseLt x h
    have hpos := hpre.topkLenNonNull x h
    have hxint : (x : Int) % 18446744073709551616 = (x : Int) :=
      Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le x) (by exact_mod_cast hlt)
    simp [compare, truncBits, BitVec.toNat_ofNat, hxint]
    omega

/-- The extra-cache length word is null exactly when the parameter has no runtime length. -/
theorem ptrIsNull_144 (P : Params) (L : Launch) (mem0 : Mem0) (hpre : Pre P L mem0) :
    Thread.ptrIsNull L 144 = !P.extraTopkLenBase.isSome := by
  cases h : P.extraTopkLenBase with
  | none =>
    rw [Thread.ptrIsNull, Thread.paramWord_144_zero hpre h]
    rfl
  | some x =>
    rw [Thread.ptrIsNull, Thread.paramWord_144_some hpre h]
    have hlt := hpre.extraTopkLenBaseLt x h
    have hpos := hpre.extraTopkLenNonNull x h
    have hxint : (x : Int) % 18446744073709551616 = (x : Int) :=
      Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le x) (by exact_mod_cast hlt)
    simp [compare, truncBits, BitVec.toNat_ofNat, hxint]
    omega

/-- The index role's launch test holds for every thread of a launched grid. -/
theorem launchTest_of_pre {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {g : Nat} (_hg : g < L.threads) : Wg1Index.LaunchTest P L g where
  ptrOrig := ptrIsNull_80 P L mem0 hpre
  ptrExtra := ptrIsNull_144 P L mem0 hpre
  noExit := geBatch_false hpre

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Interface

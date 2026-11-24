-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Kernels.Fp16Gemm8192.Spec
public import Kernels.Fp16Gemm8192.Proof.Support.Geometry
public import Kernels.Fp16Gemm8192.Proof.Support.TmaMma
public import Lemmas.TensorStore.TensorStoreSize
public import Lemmas.Tensor.TensorAddress

@[expose] public section

/-! Global byte addresses selected by the unchanged production tensor maps.

These are address and launch-allocation facts. No shared-memory contents, completed
copy, or synchronization relation is assumed or established here.
-/
namespace PTX.Kernels.Fp16Gemm8192
open PTX TensorDescriptor
noncomputable section

/-- The instruction operand order is inner coordinate, then outer coordinate. -/
def tensorOrigin (inner outer : Nat) : Fin 2 → Int :=
  fun axis => if axis.val = 0 then (inner : Int) else (outer : Int)

private theorem tensor_coord {boxInner boxOuter ox oy x y : Nat}
    {base : Nat} {sw : TensorSwizzle.Mode} {cls : AllocationClass} :
    TensorTile.coord (encodeTiled .f16 base 8192 8192 16384 boxInner boxOuter sw cls).box
      (tensorOrigin ox oy) (fun axis => if axis.val = 0 then x else y) =
        tensorOrigin (ox+x) (oy+y) := by
  funext axis
  fin_cases axis <;> simp [TensorTile.coord,TensorTile.step,encodeTiled,tensorOrigin]

/-- A single lookup lemma covers all three production maps; their boxes and
shared swizzles do not change the global row-major address calculation. -/
theorem tensor_lookup_element {base row col byte boxInner boxOuter : Nat}
    {sw : TensorSwizzle.Mode} {cls : AllocationClass}
    (hr : row < 8192) (hc : col < 8192) (hb : byte < 2) :
    TensorAddress.lookup
      (geometry (encodeTiled .f16 base 8192 8192 16384 boxInner boxOuter sw cls))
      (tensorOrigin col row) byte = some ((elementLoc base row col).at byte).addr := by
  apply (TensorAddress.lookup_some_iff _ _ _ _).mpr
  refine ⟨?_,hb,?_⟩
  · intro axis
    fin_cases axis
    · simp only [geometry,encodeTiled,tensorOrigin,ite_true]
      exact ⟨Int.natCast_nonneg _,by omega⟩
    · simp only [geometry,encodeTiled,tensorOrigin,show (1:Nat) ≠ 0 by decide,ite_false]
      exact ⟨Int.natCast_nonneg _,by omega⟩
  · have hzero : Fin.cases Format.f16.bytes (fun _ : Fin 1 => 16384) (0:Fin 2) = 2 := rfl
    have hone : Fin.cases Format.f16.bytes (fun _ : Fin 1 => 16384) (1:Fin 2) = 16384 := by
      rw [←Fin.succ_zero_eq_one,Fin.cases_succ]
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_two]
    simp only [hzero,hone,tensorOrigin,
      Fin.val_zero,Fin.val_one,ite_true,show (1:Nat) ≠ 0 by decide,ite_false,
      Int.toNat_natCast,elementLoc,Loc.at,geometry,encodeTiled]
    omega

private theorem store_writeLoc_of_lookup {d : Descriptor 1} {origin : Fin 2 → Int} {sh : Loc}
    {x y byte address : Nat}
    (hx : x < TensorTile.count d.box 0)
    (hy : y < TensorTile.count d.box 1) (hb : byte < d.format.bytes)
    (hl : TensorAddress.lookup (geometry d)
      (TensorTile.coord d.box origin (fun axis => if axis.val = 0 then x else y))
      byte = some address) :
    TensorStore.writeLoc ⟨⟨1, d, origin, sh, none⟩, none⟩ x y byte = some ⟨.global,0,address⟩ := by
  have hy' : y < TensorTile.rows d.box := hy
  unfold TensorStore.writeLoc TensorTransfer.slotAt
  rw [dite_eq_left hx,dite_eq_left hy',dite_eq_left hb]
  have hindex : TensorTransfer.index
      (⟨⟨x,hx⟩,⟨y,hy'⟩,⟨byte,hb⟩⟩ : TensorTransfer.Slot d) =
      (fun axis => if axis.val = 0 then x else y) := by
    funext axis; fin_cases axis <;> rfl
  change (TensorAddress.lookup (geometry d)
    (TensorTile.coord d.box origin (TensorTransfer.index
      (⟨⟨x,hx⟩,⟨y,hy'⟩,⟨byte,hb⟩⟩ : TensorTransfer.Slot d)))
    byte).map (fun a => (⟨.global,0,a⟩ : Loc)) = some ⟨.global,0,address⟩
  rw [hindex,hl]
  rfl

private theorem store_writeLoc_element {d : Descriptor 1} {origin : Fin 2 → Int} {sh : Loc}
    {base ox oy x y byte boxInner boxOuter : Nat} {sw : TensorSwizzle.Mode}
    {cls : AllocationClass}
    (hd : d = encodeTiled .f16 base 8192 8192 16384 boxInner boxOuter sw cls)
    (ho : origin = tensorOrigin ox oy) (hx : x < boxInner) (hy : y < boxOuter)
    (hb : byte < 2) (hr : oy+y < 8192) (hc : ox+x < 8192) :
    TensorStore.writeLoc ⟨⟨1, d, origin, sh, none⟩, none⟩ x y byte =
      some ((elementLoc base (oy+y) (ox+x)).at byte) := by
  apply store_writeLoc_of_lookup
  · simpa [hd,encodeTiled,TensorTile.count,TensorTile.step] using hx
  · simpa [hd,encodeTiled,TensorTile.count,TensorTile.step] using hy
  · simpa [hd,encodeTiled,Format.bytes] using hb
  · subst hd ho
    rw [tensor_coord]
    exact tensor_lookup_element hr hc hb

/-- One of eight 32-column output slices. -/
def outputOrigin (task rank consumer slice : Nat) : Fin 2 → Int :=
  tensorOrigin (outputCol (tileN task) slice 0) (outputRow (tileM task) rank consumer 0)

/-- Every selected output byte has the intended in-bounds D matrix destination. -/
theorem output_writeLoc {base task rank consumer slice x y byte : Nat}
    {cls : AllocationClass} {shared : Loc}
    (ht : task < 512) (hrank : rank < 2) (hconsumer : consumer < 2)
    (hs : slice < 8) (hx : x < 32) (hy : y < 128) (hb : byte < 2) :
    TensorStore.writeLoc
      ⟨⟨1, Fp16Gemm8192.mapD base cls, outputOrigin task rank consumer slice, shared, none⟩,
        none⟩ x y byte =
      some ((elementLoc base (outputRow (tileM task) rank consumer y)
        (outputCol (tileN task) slice x)).at byte) := by
  have hrow := outputRow_lt (tileM_lt ht) hrank hconsumer hy
  have hcol := outputCol_lt (tileN_lt task) hs hx
  have h := store_writeLoc_element
    (d := Fp16Gemm8192.mapD base cls) (origin := outputOrigin task rank consumer slice)
    (sh := shared)
    (hd := rfl) (ho := rfl) hx hy hb
    (show outputRow (tileM task) rank consumer 0+y < 8192 by
      simpa [outputRow] using hrow)
    (show outputCol (tileN task) slice 0+x < 8192 by
      simpa [outputCol] using hcol)
  simpa only [outputRow,outputCol,Nat.add_zero] using h

end
end PTX.Kernels.Fp16Gemm8192

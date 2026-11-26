-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.MatrixExec

@[expose] public section

/-! # The results of a warp-level matrix instance

A proof tool for appending the instance of a warp-level matrix instruction (`ldmatrix`,
`stmatrix`, `movmatrix`, `mma.sync`) to the 32 lanes of a warp (`Lemmas/Snoc/MatrixAppend.lean`).

`Consistent.matrix` (`MatrixOk`, DEP-WARP-MATRIX) constrains the bytes a lane receives by
`matrixRecv` of the instance. `MatrixRecvOk` is that clause for one lane and `MatrixResultOk` for
all 32 lanes of an instance, whatever contributions are attributed to the lane indices from 32 on
(`MatrixInstance` fixes the contributions of the lanes below 32 only).

A result that cannot be computed constrains nothing (the instance is then undefined behaviour,
`MatrixUnsafe`), so results exist for every form whose results read the 32 lanes only
(`MatrixOp.LaneClosed`, `exists_matrixResultOk`): a matrix store, a matrix load of at most 32
rows, `movmatrix`, and an MMA without sparsity metadata (`matrixRecv_congr`). The forms of the
manual's syntax lines (`MatrixMove.supported`) have at most 32 rows. -/

namespace PTX
noncomputable section

/-- The clause of `Consistent.matrix` (`MatrixOk`) for one lane: `recv` is what lane `l` may
receive in an instance of operation `op` with contributions `parts`. These are the bytes
`matrixRecv` computes, any bytes of 8-bit integers for an open result, and any bytes when the
result cannot be computed (the instance is then `MatrixUnsafe`). -/
def MatrixRecvOk (A : List Assumption) (op : MatrixOp) (parts : Nat → List (Option Byte))
    (l : Nat) (recv : List (Option Byte)) : Prop :=
  match matrixRecv A op parts l with
  | .ok (.bytes bs) => recv = bs
  | .ok (.open_ m) => OpenBytes m recv
  | .error _ => True

/-- The bytes `recv l` are results of the instance of `op` in which each lane `l < 32`
contributes `parts l`: the clause of `MatrixOk` for every lane, whatever is attributed to the
indices from 32 on. -/
def MatrixResultOk (A : List Assumption) (op : MatrixOp)
    (parts recv : Nat → List (Option Byte)) : Prop :=
  ∀ parts', (∀ l < 32, parts' l = parts l) → ∀ l < 32, MatrixRecvOk A op parts' l (recv l)

variable {A : List Assumption} {op : MatrixOp} {parts parts' : Nat → List (Option Byte)}
  {l : Nat}

/-- The bytes `matrixRecv` computes satisfy the clause of the lane. -/
theorem MatrixRecvOk.of_bytes {bs : List (Option Byte)}
    (h : matrixRecv A op parts l = .ok (.bytes bs)) : MatrixRecvOk A op parts l bs := by
  unfold MatrixRecvOk
  rw [h]

/-- **A lane always has a result**: the computed bytes, bytes of zero for an open result, and
anything when the result cannot be computed. -/
theorem exists_matrixRecvOk (A : List Assumption) (op : MatrixOp)
    (parts : Nat → List (Option Byte)) (l : Nat) : ∃ recv, MatrixRecvOk A op parts l recv := by
  unfold MatrixRecvOk
  cases matrixRecv A op parts l with
  | error f => exact ⟨[], trivial⟩
  | ok r =>
    cases r with
    | bytes bs => exact ⟨bs, rfl⟩
    | open_ m =>
      refine ⟨List.replicate m (some (.bits 8 0, 0)), List.length_replicate, fun b hb => ?_⟩
      exact ⟨0, List.eq_of_mem_replicate hb⟩

/-- The forms whose results read the contributions of the 32 lanes only: a matrix store, a matrix
load of at most 32 rows (every supported form), `movmatrix`, and an MMA without sparsity
metadata. -/
def MatrixOp.LaneClosed : MatrixOp → Prop
  | .move m => m.store = true ∨ m.num * m.rows ≤ 32
  | .transpose => True
  | .mma s => s.sparse = none

instance (op : MatrixOp) : Decidable op.LaneClosed := by
  cases op <;> unfold MatrixOp.LaneClosed <;> infer_instance

/-- Every matrix load or store of the manual's syntax lines (`MatrixMove.supported`) has at most
32 rows, so its results read the 32 lanes only. -/
theorem MatrixOp.laneClosed_of_supported {m : MatrixMove} (h : m.supported = true) :
    (MatrixOp.move m).LaneClosed := by
  refine .inr ?_
  unfold MatrixMove.supported at h
  unfold MatrixMove.rows
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
  obtain ⟨hn, -⟩ := h
  cases hs : m.shape <;> simp only [hs] at hn ⊢ <;>
    rcases hn with (h | h) | ⟨h, hne⟩ <;> first | omega | exact absurd rfl hne

/-- The row of a byte of a matrix load of at most 32 rows is supplied by one of the 32 lanes. -/
theorem MatrixMove.source_lane_lt (m : MatrixMove) (hm : m.num * m.rows ≤ 32) {l x : Nat}
    (hl : l < 32) (hx : x < m.num * m.regsPerMatrix * 4) :
    (m.source l (x / 4) (x % 4)).1 < 32 := by
  unfold MatrixMove.source
  unfold MatrixMove.rows at hm
  unfold MatrixMove.regsPerMatrix at hx
  cases hs : m.shape <;> cases ht : m.trans <;> simp only [hs] at hm hx ⊢ <;> omega

/-- The byte a supplier receives in a matrix store is a byte of one of the 32 lanes. -/
theorem MatrixMove.storeByte_congr (m : MatrixMove) (h : ∀ l < 32, parts' l = parts l)
    (row k : Nat) : m.storeByte parts' row k = m.storeByte parts row k := by
  unfold MatrixMove.storeByte
  simp only
  cases hf : ((List.range 32).flatMap fun l =>
      (List.range (m.num * m.regsPerMatrix * 4)).map (l, ·)).find?
      (fun (l, x) => m.source l (x / 4) (x % 4) == (row, k)) with
  | none => rfl
  | some lx =>
    obtain ⟨l', x⟩ := lx
    have hmem := List.mem_of_find?_eq_some hf
    obtain ⟨l0, hl0, hmap⟩ := List.mem_flatMap.mp hmem
    obtain ⟨x0, -, he⟩ := List.mem_map.mp hmap
    cases he
    simp only [h l' (List.mem_range.mp hl0)]

/-- An element of an MMA operand is read from one of the 32 lanes. -/
theorem operandElem_congr (h : ∀ l < 32, parts' l = parts l)
    (f : Nat → Nat → Nat × Nat × Nat) (n off : Nat) (ty : DType) (pos : Nat × Nat × Nat) :
    operandElem parts' f n off ty pos = operandElem parts f n off ty pos := by
  unfold operandElem
  cases hf : findFrag f n pos with
  | none => rfl
  | some li =>
    obtain ⟨l', i⟩ := li
    unfold findFrag at hf
    have hmem := List.mem_of_find?_eq_some hf
    obtain ⟨l0, hl0, hmap⟩ := List.mem_flatMap.mp hmem
    obtain ⟨i0, -, he⟩ := List.mem_map.mp hmap
    cases he
    simp only [h l' (List.mem_range.mp hl0)]

/-- **The result of a lane depends on the contributions of the 32 lanes only**, for the forms of
`MatrixOp.LaneClosed`. -/
theorem matrixRecv_congr (hop : op.LaneClosed) (h : ∀ l < 32, parts' l = parts l)
    (hl : l < 32) : matrixRecv A op parts' l = matrixRecv A op parts l := by
  cases op with
  | move m =>
    simp only [matrixRecv, matrixMoveRecv]
    by_cases hst : m.store = true
    · have hsb : m.storeByte parts' = m.storeByte parts := by
        funext row k
        exact m.storeByte_congr h row k
      simp only [hst, ite_true, hsb]
    · have hm : m.num * m.rows ≤ 32 := hop.resolve_left hst
      simp only [hst, ite_false, Bool.false_eq_true]
      cases hfmt : m.fmt <;> simp only <;> congr 2 <;>
        refine List.map_congr_left fun x hx => ?_
      all_goals
        simp only [h _ (m.source_lane_lt hm hl (List.mem_range.mp hx))]
  | transpose =>
    simp only [matrixRecv, transposeRecv]
    congr 2
    refine List.map_congr_left fun b hb => ?_
    have hb' := List.mem_range.mp hb
    have hsrc : (transposeSource l b).1 < 32 := by
      unfold transposeSource
      simp only
      omega
    simp only [h _ hsrc]
  | mma s =>
    have hsp : s.sparse = none := hop
    have ha : operandElem parts' = operandElem parts := by
      funext f n off ty pos
      exact operandElem_congr h f n off ty pos
    simp only [matrixRecv, mmaRecv, hsp, ha]

/-- **Results exist** for an instance of a form of `MatrixOp.LaneClosed`. -/
theorem exists_matrixResultOk (A : List Assumption) (hop : op.LaneClosed)
    (parts : Nat → List (Option Byte)) : ∃ recv, MatrixResultOk A op parts recv := by
  choose recv hrecv using fun l => exists_matrixRecvOk A op parts l
  refine ⟨recv, fun parts' hp l hl => ?_⟩
  unfold MatrixRecvOk
  rw [matrixRecv_congr hop hp hl]
  exact hrecv l

/-- For a form of `MatrixOp.LaneClosed`, the lanes' clauses for the given contributions give the
results of the instance. -/
theorem MatrixResultOk.of_lanes {recv : Nat → List (Option Byte)} (hop : op.LaneClosed)
    (h : ∀ l < 32, MatrixRecvOk A op parts l (recv l)) : MatrixResultOk A op parts recv := by
  intro parts' hp l hl
  unfold MatrixRecvOk
  rw [matrixRecv_congr hop hp hl]
  exact h l hl

/-- For a form of `MatrixOp.LaneClosed`, the bytes `matrixRecv` computes for every lane are the
results of the instance (the defined case: no lane's result is an error). -/
theorem MatrixResultOk.of_bytes {recv : Nat → List (Option Byte)} (hop : op.LaneClosed)
    (h : ∀ l < 32, matrixRecv A op parts l = .ok (.bytes (recv l))) :
    MatrixResultOk A op parts recv :=
  .of_lanes hop fun l hl => .of_bytes (h l hl)

end
end PTX

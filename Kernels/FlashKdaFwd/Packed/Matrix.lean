-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Activation
public import Lemmas.Tcgen05.MemFloat
public import Lemmas.Flow.Scalars
import Mathlib.Tactic.FinCases
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Matrix
open PTX PTX.Assumption

def shape : MmaSpec :=
  {m := 16, n := 8, k := 16, types := ⟨.float .bf16, .float .bf16, .float .f32, .float .f32, none⟩}

abbrev Tile := Nat → Nat → ℝ

def value (fmt : FloatFmt) (a : Tile) (pos : Nat × Nat × Nat) : Value :=
  .float fmt (a pos.2.1 pos.2.2)

def bytes (v : Value) : List (Option Byte) := v.toBytes.map some

inductive Accumulator where
  | zeroWord
  | prior (tile : Tile)

def Accumulator.atCell : Accumulator → Nat × Nat × Nat → Value
  | .zeroWord, _ => .bits 32 0
  | .prior c, p => value .f32 c p

def Accumulator.tile : Accumulator → Tile
  | .zeroWord => fun _ _ => 0
  | .prior c => c

def inputBytes (a b : Tile) (c : Accumulator) (l : Nat) : List (Option Byte) :=
  (List.range 8).flatMap (fun i => bytes (value .bf16 a (shape.fragA l i))) ++
  (List.range 4).flatMap (fun i => bytes (value .bf16 b (shape.fragB l i))) ++
  (List.range 4).flatMap (fun i => bytes (c.atCell (shape.fragCD (.float .f32) l i)))

def laneBytes (a b c : Tile) := inputBytes a b (.prior c)

private theorem read_value (fmt : FloatFmt) (x : ℝ) :
    rebuild 3 (bytes (.float fmt x)) = .ok (.float fmt x) := by
  have h := rebuild_scalar (v := .float fmt x) (fun _ => rfl)
    (by change 0 < fmt.bytes; cases fmt <;> decide)
  simpa only [bytes, Value.toBytes, List.map_map, Function.comp_def, Value.byteAt] using h

private theorem byte_a (a b : Tile) (c : Accumulator) (l : Nat) (i : Fin 8) :
    mmaElem (inputBytes a b c l) 0 (.float .bf16) i = .ok (value .bf16 a (shape.fragA l i)) := by
  have h : ((inputBytes a b c l).drop (2*i.val)).take 2 =
      bytes (value .bf16 a (shape.fragA l i)) := by fin_cases i <;> rfl
  change rebuild 3 (((inputBytes a b c l).drop (0 + i.val*2)).take 2) = _
  rw [Nat.zero_add, Nat.mul_comm, h]
  exact read_value _ _

private theorem byte_b (a b : Tile) (c : Accumulator) (l : Nat) (i : Fin 4) :
    mmaElem (inputBytes a b c l) 16 (.float .bf16) i = .ok (value .bf16 b (shape.fragB l i)) := by
  have h : ((inputBytes a b c l).drop (16+i.val*2)).take 2 =
      bytes (value .bf16 b (shape.fragB l i)) := by fin_cases i <;> rfl
  change rebuild 3 (((inputBytes a b c l).drop (16+i.val*2)).take 2) = _
  rw [h]
  exact read_value _ _

private theorem byte_c (a b : Tile) (c : Accumulator) (l : Nat) (i : Fin 4) :
    mmaElem (inputBytes a b c l) 24 (.float .f32) i =
      .ok (c.atCell (shape.fragCD (.float .f32) l i)) := by
  have h : ((inputBytes a b c l).drop (24+i.val*4)).take 4 =
      bytes (c.atCell (shape.fragCD (.float .f32) l i)) := by cases c <;> fin_cases i <;> rfl
  change rebuild 3 (((inputBytes a b c l).drop (24+i.val*4)).take 4) = _
  rw [h]
  cases c with
  | prior c => exact read_value _ _
  | zeroWord => exact rebuild_scalar (v := .bits 32 0) (fun _ => rfl) (by decide)

private theorem lookup {parts : Nat → List (Option Byte)} {f : Nat → Nat → Nat × Nat × Nat}
    {n off : Nat} {ty : DType} {pos : Nat × Nat × Nat} {v : (Nat × Nat × Nat) → Value}
    (cover : ∃ l < 32, ∃ i < n, f l i = pos)
    (reads : ∀ l, ∀ i < n, mmaElem (parts l) off ty i = .ok (v (f l i))) :
    operandElem parts f n off ty pos = .ok (v pos) := by
  let cells := (List.range 32).flatMap fun l => (List.range n).map (l, ·)
  let accepts := fun p : Nat × Nat => f p.1 p.2 == pos
  have in_cells (l i : Nat) : (l,i) ∈ cells ↔ l < 32 ∧ i < n := by simp [cells]
  obtain ⟨l, hl, i, hi, hp⟩ := cover
  have present := List.find?_isSome.mpr
    (⟨(l,i), (in_cells ..).mpr ⟨hl,hi⟩, by simp [accepts, hp]⟩ :
      ∃ p, p ∈ cells ∧ accepts p)
  cases found : cells.find? accepts with
  | none => simp [found] at present
  | some p =>
    have hit : accepts p := List.find?_some found
    have exactPos : f p.1 p.2 = pos := eq_of_beq hit
    have valid := (in_cells p.1 p.2).mp (List.mem_of_find?_eq_some found)
    unfold operandElem
    change (match cells.find? accepts with
      | some (j, k) => mmaElem (parts j) off ty k | none => Except.error Fault.noRule) = _
    rw [found, ← exactPos]
    exact reads _ _ valid.2

theorem read_a (a b : Tile) (c : Accumulator) (r k : Nat) (hr : r < 16) (hk : k < 16) :
    operandElem (inputBytes a b c) shape.fragA 8 0 (.float .bf16) (0,r,k) =
      .ok (.float .bf16 (a r k)) := by
  apply lookup (v := value .bf16 a)
  · refine ⟨4*(r%8) + k%8/2, by omega, 4*(k/8) + 2*(r/8) + k%2, by omega, ?_⟩
    simp [MmaSpec.fragA, shape, MmaSpec.quad, MmaSpec.perReg, MmaSpec.regBits, DType.width]
    omega
  · exact fun l i hi => byte_a a b c l ⟨i,hi⟩

theorem read_b (a b : Tile) (c : Accumulator) (k j : Nat) (hk : k < 16) (hj : j < 8) :
    operandElem (inputBytes a b c) shape.fragB 4 16 (.float .bf16) (0,k,j) =
      .ok (.float .bf16 (b k j)) := by
  apply lookup (v := value .bf16 b)
  · refine ⟨4*j + k%8/2, by omega, 2*(k/8) + k%2, by omega, ?_⟩
    simp [MmaSpec.fragB, shape, MmaSpec.quad, MmaSpec.perReg, MmaSpec.regBits, DType.width]
    omega
  · exact fun l i hi => byte_b a b c l ⟨i,hi⟩

theorem read_c (a b : Tile) (c : Accumulator) (r j : Nat) (hr : r < 16) (hj : j < 8) :
    operandElem (inputBytes a b c) (shape.fragCD (.float .f32)) 4 24 (.float .f32) (0,r,j) =
      .ok (c.atCell (0,r,j)) := by
  apply lookup (v := c.atCell)
  · refine ⟨4*(r%8) + j/2, by omega, 2*(r/8) + j%2, by omega, ?_⟩
    simp [MmaSpec.fragCD, shape, MmaSpec.quad]
    omega
  · exact fun l i hi => byte_c a b c l ⟨i,hi⟩

theorem operand_a (a b c : Tile) (r k : Nat) (hr : r < 16) (hk : k < 16) :
    operandElem (laneBytes a b c) shape.fragA 8 0 (.float .bf16) (0,r,k) =
      .ok (.float .bf16 (a r k)) := read_a a b (.prior c) r k hr hk

theorem operand_b (a b c : Tile) (k j : Nat) (hk : k < 16) (hj : j < 8) :
    operandElem (laneBytes a b c) shape.fragB 4 16 (.float .bf16) (0,k,j) =
      .ok (.float .bf16 (b k j)) := read_b a b (.prior c) k j hk hj

theorem operand_c (a b c : Tile) (r j : Nat) (hr : r < 16) (hj : j < 8) :
    operandElem (laneBytes a b c) (shape.fragCD (.float .f32)) 4 24 (.float .f32) (0,r,j) =
      .ok (.float .f32 (c r j)) := read_c a b (.prior c) r j hr hj

private theorem map_reads {α β : Type} (xs : List α) (f : α → Exec β) (v : α → β)
    (h : ∀ i ∈ xs, f i = .ok (v i)) : xs.mapM f = .ok (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, h x (by simp), ih (fun i hi => h i (by simp [hi]))]
    rfl

def dot (a b c : Tile) (r j : Nat) : ℝ :=
  ((List.range 16).map (fun k => a r k * b k j)).sum + c r j

private theorem products (xs : List (ℝ × ℝ)) :
    ((xs.map (fun p => Value.float .bf16 p.1)).zip
        (xs.map (fun p => Value.float .bf16 p.2))).mapM (fun (x,y) => do
      pure ((← idealWarpElem (.float .bf16) x) * (← idealWarpElem (.float .bf16) y))) =
      .ok (xs.map fun (x,y) => x*y) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, ih]
    rfl

private theorem multiply (xs : List (ℝ × ℝ)) (cv : Value) (z : ℝ) (hc : valFloat .f32 cv = .ok z) :
    mmaValue [Activation.arithmetic, Activation.approximate] shape
        (xs.map fun p => .float .bf16 p.1) (xs.map fun p => .float .bf16 p.2) cv =
      .ok (.float .f32 ((xs.map fun p => p.1*p.2).sum + z)) := by
  change (do
    let ps : List ℝ ← _
    let c ← valFloat .f32 cv
    pure (Value.float .f32 (ps.sum + c))) = _
  simp only [shape] at *
  rw [products xs, hc]
  rfl

private def pairValues (p : ℝ × ℝ) : Value × Value :=
  (.float .bf16 p.1, .float .bf16 p.2)

private noncomputable def pairs (parts : Nat → List (Option Byte)) (r j : Nat) :
    Exec (List (Value × Value)) :=
  (List.range 16).mapM fun k => do
    pure (← operandElem parts shape.fragA 8 0 (.float .bf16) (0,r,k),
          ← operandElem parts shape.fragB 4 16 (.float .bf16) (0,k,j))

private theorem read_pairs (a b : Tile) (c : Accumulator) (r j : Nat) (hr : r < 16) (hj : j < 8) :
    pairs (inputBytes a b c) r j =
      .ok (((List.range 16).map (fun k => (a r k,b k j))).map pairValues) := by
  unfold pairs
  rw [List.map_map]
  apply map_reads
  intro k hk
  have h := List.mem_range.mp hk
  simp only [read_a a b c r k hr h, read_b a b c k j h hj]
  rfl

private noncomputable def cell (parts : Nat → List (Option Byte)) (r j : Nat) : Exec Value := do
  let ab ← pairs parts r j
  let z ← operandElem parts (shape.fragCD (.float .f32)) 4 24 (.float .f32) (0,r,j)
  let v ← mmaValue [Activation.arithmetic, Activation.approximate] shape
    (ab.map (·.1)) (ab.map (·.2)) z
  unless v.bytes = 4 do throw .typeMismatch
  pure v

private theorem read_cell (a b : Tile) (c : Accumulator) (r j : Nat) (hr : r < 16) (hj : j < 8) :
    cell (inputBytes a b c) r j = .ok (.float .f32 (dot a b c.tile r j)) := by
  let xs := (List.range 16).map (fun k => (a r k, b k j))
  unfold cell
  rw [read_pairs a b c r j hr hj, read_c a b c r j hr hj]
  change (do
    let v ← mmaValue [Activation.arithmetic, Activation.approximate] shape
      ((xs.map pairValues).map Prod.fst) ((xs.map pairValues).map Prod.snd) (c.atCell (0,r,j))
    unless v.bytes = 4 do throw Fault.typeMismatch
    pure v) = _
  simp only [List.map_map, Function.comp_def, pairValues]
  have hc : valFloat .f32 (c.atCell (0,r,j)) = .ok (c.tile r j) := by
    cases c with
    | prior _ => rfl
    | zeroWord => exact PTX.Proof.valFloat_z0
  rw [multiply xs _ _ hc]
  change Except.ok (Value.float .f32 ((xs.map (fun p => p.1*p.2)).sum+c.tile r j)) = _
  simp [xs, dot, List.map_map, Function.comp_def]

def row (l i : Nat) := l / 4 + 8 * (i / 2)

def col (l i : Nat) := 2 * (l % 4) + i % 2

def result (a b c : Tile) (l : Nat) :=
  (List.range 4).flatMap fun i => bytes (.float .f32 (dot a b c (row l i) (col l i)))

theorem receive_words (a b : Tile) (c : Accumulator) (l : Nat) (hl : l < 32) :
    mmaRecv [Activation.arithmetic, Activation.approximate] shape (inputBytes a b c) l =
      .ok (result a b c.tile l) := by
  let v := fun i => Value.float .f32 (dot a b c.tile (row l i) (col l i))
  have vals : (List.range 4).mapM (fun i => cell (inputBytes a b c) (row l i) (col l i)) =
      .ok ((List.range 4).map v) := by
    apply map_reads
    intro i hi
    have hi := List.mem_range.mp hi
    exact read_cell a b c _ _ (by unfold row; omega) (by unfold col; omega)
  change (do
    let vals ← (List.range 4).mapM (fun i => cell (inputBytes a b c) (row l i) (col l i))
    let regs := (List.range 4).map fun r => match (vals.drop (1*r)).take 1 with
      | [lo, hi] => Value.pair lo hi
      | x :: _ => x
      | [] => .bits 0 0
    pure (regs.flatMap bytes)) = _
  rw [vals]
  rfl

theorem receive (a b c : Tile) (l : Nat) (hl : l < 32) :
    mmaRecv [Activation.arithmetic, Activation.approximate] shape (laneBytes a b c) l =
      .ok (result a b c l) := receive_words a b (.prior c) l hl

theorem event_result (L : Launch) (X : Execution) (a b c : Tile) {g i pc n own recv}
    (consistent : MatrixOk L [Activation.arithmetic, Activation.approximate] X)
    (event : X.get (g,i) = some ⟨pc, .matrix (.mma shape) own recv⟩) (index : X.MatrixK (g,i) n)
    (inputs : MatrixInstance L X g n pc (.mma shape) (laneBytes a b c)) :
    recv = result a b c (laneOf L g) := by
  have h := consistent _ _ _ _ _ _ _ event index _ inputs
  have lane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  simp only [matrixRecv, receive a b c (laneOf L g) lane] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 8000000 in
theorem first_site : Transfers.slice 2199 1 = some [⟨none, .matrix {
    op := .mma shape, dsts := [1188,1189,1190,1191],
    srcs := [1162,1163,1164,1165,1166,1167,1168,1168,1168,1168].map Opnd.reg }⟩] := by rfl

end FlashKda.Packed.Matrix

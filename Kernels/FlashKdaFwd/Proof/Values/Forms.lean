-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.FragmentsLayout
public import Kernels.FlashKdaFwd.Proof.Values.Raw
public import Kernels.FlashKdaFwd.Proof.Thread.DataLib

@[expose] public section

/-!
# Value forms: what a data register of a compute lane holds

The register table of the tile loop (`Gen/Tables/matrix_table.json`, made by
`Gen/matrix_table.py`) gives every data register a *form*: a lane-independent description such
as "A register 2 of the block 3 of `k_decayed`". This file is the Lean side of that vocabulary.

* `Mat` names the real matrices of one tile for a warp (the terms of `Math/Fragments.lean`);
  `Mat.eval x w` is the matrix, for the arrays `x : Inputs` of the tile and the warp number `w`.
  A *half* is eight consecutive value channels; `bi` (0 or 1) and `q` (0 or 1) name the half
  `halfBase w bi q` of the warp.
* `Form` is the form of one register; `Form.Holds x w l f v` says that the value `v` is what the
  form `f` denotes in lane `l` of warp `w`. For registers of payloads this is an equation with
  the literal value the library's multiply-accumulate lemmas ask for (`WarpMatrix.regA`, `regB`,
  `regC`: packed pairs of bfloat16 payloads and FP32 payloads); for the registers that hold raw
  bfloat16 bit patterns of `v` and of the gate logits it is the predicate of
  `Proof/Values/Raw.lean` (a bit pattern, or the payload zero of an out-of-bounds load).
* A `Table` is a list of registers with their forms, in ascending register order (the registers
  live at one program point); `Table.Holds` says a slot file satisfies it. `Table.step` moves a
  table across an event that writes the registers `ds`: each entry of the new table is a written
  register with its new form or an entry of the old table (a one-pass Boolean check,
  `Table.sub`), and the written values satisfy the new forms.

Register numbers are the machine's register ids (`%rN` is `306 + N`, `%rsN` is `89 + N`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.Kernels.FlashKdaFwd.Recurrence (multiplier)

noncomputable section

/-- The two tile arrays of phase 1: `k_decayed` and `q_decayed`. -/
inductive Arr where
  | kd
  | qd
  deriving DecidableEq, Repr

/-- The array of the inputs that `a` names. -/
def Arr.get (x : Inputs) : Arr → ℕ → ℕ → ℝ
  | .kd => x.decayedKey
  | .qd => x.decayedQuery

/-- A real matrix of one tile, by name. `m` is a key block (0 to 7), `n` a number of key blocks
already accumulated, `bi` and `q` the value block and the half of the warp. -/
inductive Mat where
  /-- `keyBlock a m`: the A operand of phase 1. -/
  | keyBlock (a : Arr) (m : ℕ)
  /-- `keyBlockT x.restoredKey m`: the A operand of phase 6. -/
  | keyBlockT (m : ℕ)
  /-- `INV`. -/
  | inv
  /-- `Mqk`. -/
  | mqk
  /-- `stateBlock x.copy (halfBase w bi q) m`: the B operand of phase 1. -/
  | stateBlock (bi q m : ℕ)
  /-- `project a x.copy (halfBase w bi q) n`: an accumulator of phase 1 after `n` key blocks. -/
  | project (a : Arr) (bi q n : ℕ)
  /-- `residual x (halfBase w bi q)`: `(v - u) * beta`. -/
  | residual (bi q : ℕ)
  /-- `correction x (halfBase w bi q)`: `U`. -/
  | correction (bi q : ℕ)
  /-- `output x (halfBase w bi q)`. -/
  | output (bi q : ℕ)
  /-- `update x (halfBase w bi q) m`: the accumulator of the state update of key block `m`. -/
  | update (bi q m : ℕ)
  /-- `nextState x (halfBase w bi q) m`: the new state of key block `m`. -/
  | nextState (bi q m : ℕ)
  deriving DecidableEq, Repr

/-- The matrix that `M` names, for the arrays `x` of the tile and warp `w`. -/
def Mat.eval (x : Inputs) (w : ℕ) : Mat → ℕ → ℕ → ℝ
  | .keyBlock a m => Math.Fragments.keyBlock (a.get x) m
  | .keyBlockT m => Math.Fragments.keyBlockT x.restoredKey m
  | .inv => x.inverse
  | .mqk => x.score
  | .stateBlock bi q m => Math.Fragments.stateBlock x.copy (halfBase w bi q) m
  | .project a bi q n => Math.Fragments.project (a.get x) x.copy (halfBase w bi q) n
  | .residual bi q => Math.Fragments.residual x (halfBase w bi q)
  | .correction bi q => Math.Fragments.correction x (halfBase w bi q)
  | .output bi q => Math.Fragments.output x (halfBase w bi q)
  | .update bi q m => Math.Fragments.update x (halfBase w bi q) m
  | .nextState bi q m => Math.Fragments.nextState x (halfBase w bi q) m

/-- The form of one data register (the vocabulary of the register table; `r` is the index of
the register in its group, `e` selects the row `l / 4` or `l / 4 + 8`). -/
inductive Form where
  /-- A register `r` (0 to 3) of the matrix: a packed pair of bfloat16 payloads. -/
  | regA (M : Mat) (r : ℕ)
  /-- B register `r` (0 or 1) of the matrix: a packed pair of bfloat16 payloads. -/
  | regB (M : Mat) (r : ℕ)
  /-- Accumulator register `r` (0 to 3) of the matrix: an FP32 payload. -/
  | regC (M : Mat) (r : ℕ)
  /-- The narrowed accumulator registers `2 p` and `2 p + 1` packed into one register. -/
  | rowPair (M : Mat) (p : ℕ)
  /-- The narrowed accumulator register `r`: a bfloat16 payload in a 16-bit register. -/
  | narrowC (M : Mat) (r : ℕ)
  /-- Register `r` (0 to 3) of the block of `v` of value block `bi`, in the layout of an A
  operand: two bit patterns, or two payload zeros. -/
  | rawA (bi r : ℕ)
  /-- One element of `v`, at accumulator position `r` of a half: 16 bits. -/
  | vRaw16 (bi q r : ℕ)
  /-- The same, zero-extended to 32 bits. -/
  | vBitsZ (bi q r : ℕ)
  /-- The same, in the high half of a 32-bit word: it reads as the FP32 number. -/
  | vBitsH (bi q r : ℕ)
  /-- `v - u` at accumulator position `r` of a half. -/
  | diff (bi q r : ℕ)
  /-- The gate logit of row `l / 4 + 8 e`: its bit pattern zero-extended. -/
  | logitZ (e : ℕ)
  /-- The gate logit in the high half of a 32-bit word. -/
  | logitH (e : ℕ)
  /-- The logit times the constant of the gate. -/
  | logitK (e : ℕ)
  /-- Two to that power. -/
  | logitE (e : ℕ)
  /-- Plus one. -/
  | logitP (e : ℕ)
  /-- The gate strength of row `l / 4 + 8 e`. -/
  | gate (e : ℕ)
  /-- `g_total` of key feature `16 m + l / 4 + 8 e`. -/
  | decay (m e : ℕ)
  /-- The FP32 carry of key block `m`, value block `bi`, half `q`, accumulator register `r`,
  before its fused multiply-add of the tile. -/
  | carry (m bi q r : ℕ)
  deriving DecidableEq, Repr

/-- The real number of the element of `v` at accumulator position `r` of the half `(bi, q)`. -/
def vAt (x : Inputs) (w l bi q r : ℕ) : ℝ := x.value (cRow l r) (halfBase w bi q + cCol l r)

/-- The gate logit of the row `l / 4 + 8 e` of lane `l`. -/
def logitAt (x : Inputs) (l e : ℕ) : ℝ := x.logit (l / 4 + 8 * e)

/-- **What a form denotes.** `f.Holds x w l v`: the value `v` is the content the form `f`
describes, in lane `l` of warp `w`, for the arrays `x` of the tile. -/
def Form.Holds (x : Inputs) (w l : ℕ) : Form → Value → Prop
  | .regA M r, v => v = WarpMatrix.regA (M.eval x w) l r
  | .regB M r, v => v = WarpMatrix.regB (M.eval x w) l r
  | .regC M r, v => v = WarpMatrix.regC (M.eval x w) l r
  | .rowPair M p, v => v = bf16Pair (Math.Fragments.rowPair (M.eval x w) p l 0)
      (Math.Fragments.rowPair (M.eval x w) p l 1)
  | .narrowC M r, v => v = .float .bf16 (M.eval x w (cRow l r) (cCol l r))
  | .rawA bi r, v =>
      RawPair v (x.value (aRow l r) (halfBase w bi 0 + aCol l r 0))
        (x.value (aRow l r) (halfBase w bi 0 + aCol l r 1))
  | .vRaw16 bi q r, v => Bf16Of v (vAt x w l bi q r)
  | .vBitsZ bi q r, v => ∃ n < 65536, ∃ y : ℚ, v = .bits 32 (BitVec.ofNat 64 n) ∧
      FloatFmt.bf16.decode n = some y ∧ (y : ℝ) = vAt x w l bi q r
  | .vBitsH bi q r, v => v.bytes = 4 ∧ valFloat .f32 v = .ok (vAt x w l bi q r)
  | .diff bi q r, v => v = .float .f32 (vAt x w l bi q r -
      Math.Fragments.project x.decayedKey x.copy (halfBase w bi q) 8 (cRow l r) (cCol l r))
  | .logitZ e, v => ∃ n < 65536, ∃ y : ℚ, v = .bits 32 (BitVec.ofNat 64 n) ∧
      FloatFmt.bf16.decode n = some y ∧ (y : ℝ) = logitAt x l e
  | .logitH e, v => v.bytes = 4 ∧ valFloat .f32 v = .ok (logitAt x l e)
  | .logitK e, v => v = .float .f32 (logitAt x l e * ((multiplier : ℚ) : ℝ))
  | .logitE e, v => v = .float .f32 (Real.rpow 2 (logitAt x l e * ((multiplier : ℚ) : ℝ)))
  | .logitP e, v => v = .float .f32 (Real.rpow 2 (logitAt x l e * ((multiplier : ℚ) : ℝ)) + 1)
  | .gate e, v => v = .float .f32 (Math.Fragments.gate x (l / 4 + 8 * e))
  | .decay m e, v => v = .float .f32 (x.totalDecay (16 * m + l / 4 + 8 * e))
  | .carry m bi q r, v =>
      v = .float .f32 (x.carry (16 * m + cRow l r) (halfBase w bi q + cCol l r))

/-- The forms of 32-bit registers (every form but the two of 16-bit registers). -/
def Form.wide : Form → Bool
  | .narrowC .. | .vRaw16 .. => false
  | _ => true

/-- **The kind half of a form**: a 32-bit register that satisfies its form holds four bytes, so
a matrix instruction can take it as a source and a pack or a store never faults on it. -/
theorem Form.bytes {x : Inputs} {w l : ℕ} {f : Form} {v : Value} (h : f.Holds x w l v)
    (hw : f.wide = true) : v.bytes = 4 := by
  cases f <;> simp only [Form.wide, Bool.false_eq_true] at hw <;>
    simp only [Form.Holds] at h
  case regA => rw [h]; rfl
  case regB => rw [h]; rfl
  case regC => rw [h]; rfl
  case rowPair => rw [h]; rfl
  case rawA => exact h.1
  case vBitsZ => obtain ⟨n, -, y, rfl, -⟩ := h; rfl
  case vBitsH => exact h.1
  case diff => rw [h]; rfl
  case logitZ => obtain ⟨n, -, y, rfl, -⟩ := h; rfl
  case logitH => exact h.1
  case logitK => rw [h]; rfl
  case logitE => rw [h]; rfl
  case logitP => rw [h]; rfl
  case gate => rw [h]; rfl
  case decay => rw [h]; rfl
  case carry => rw [h]; rfl

/-! ## Tables -/

/-- The registers live at a program point, each with its form, in ascending register order. -/
abbrev Table := List (ℕ × Form)

/-- The slot file `val` satisfies the table: every listed register holds what its form
denotes. -/
def Table.Holds (T : Table) (x : Inputs) (w l : ℕ) (val : ℕ → Value) : Prop :=
  ∀ p ∈ T, p.2.Holds x w l (val p.1)

/-- The table lists register `r` with form `f` (a Boolean check on literal tables). -/
def Table.has (T : Table) (r : ℕ) (f : Form) : Bool := T.any fun p => p.1 == r && decide (p.2 = f)

/-- A listed register holds its form. -/
theorem Table.Holds.get {T : Table} {x : Inputs} {w l : ℕ} {val : ℕ → Value}
    (h : T.Holds x w l val) {r : ℕ} {f : Form} (hm : T.has r f = true) : f.Holds x w l (val r) := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
  have := h p hp
  rwa [hq.1, hq.2] at this

/-- Every entry of `T'` is an entry of `N` (the registers an event writes, with their new
forms) or, when `N` does not list its register, an entry of `T`: one pass over `T'` and `T`,
which are in ascending register order (`N` is short). -/
def Table.sub : Table → Table → Table → Bool
  | [], _, _ => true
  | p :: T', T, N =>
    bif N.any fun q => q.1 == p.1 then decide (p ∈ N) && Table.sub T' T N
    else match T.dropWhile fun q => Nat.blt q.1 p.1 with
      | [] => false
      | q :: T2 => decide (q = p) && Table.sub T' T2 N

theorem Table.mem_of_sub : ∀ {T' T N : Table}, Table.sub T' T N = true →
    ∀ p ∈ T', p ∈ N ∨ (p.1 ∉ N.map Prod.fst ∧ p ∈ T)
  | [], _, _, _, p, hp => by cases hp
  | p0 :: T', T, N, h, p, hp => by
    simp only [Table.sub] at h
    cases hc : N.any fun q => q.1 == p0.1
    · rw [hc, Bool.cond_false] at h
      have hk : p0.1 ∉ N.map Prod.fst := fun hm => by
        obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hm
        have : (N.any fun q => q.1 == p0.1) = true :=
          List.any_eq_true.mpr ⟨q, hq, by simpa using hq1⟩
        rw [hc] at this
        cases this
      cases hd : T.dropWhile (fun q => Nat.blt q.1 p0.1) with
      | nil => rw [hd] at h; cases h
      | cons q T2 =>
        rw [hd] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have hsuf : (q :: T2) <:+ T := hd ▸ List.dropWhile_suffix _
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact .inr ⟨hk, hsuf.subset (by rw [h.1]; exact List.mem_cons_self)⟩
        · exact (Table.mem_of_sub h.2 p hp').imp_right fun hm =>
            ⟨hm.1, hsuf.subset (List.mem_cons_of_mem _ hm.2)⟩
    · rw [hc, Bool.cond_true] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact .inl h.1
      · exact Table.mem_of_sub h.2 p hp'

/-- **A table across an event.** The event writes the values `vs` to the distinct registers
`ds` of the slot file `val`; `fs` are the forms of these registers afterwards. The new table
`T'` holds when each of its entries is one of the written registers with its new form, or an
entry of the old table `T` at a register that is not written (`hsub`, a Boolean check), and the
written values satisfy the new forms (`hnew`). -/
theorem Table.step {T T' : Table} {x : Inputs} {w l : ℕ} {val : ℕ → Value} {ds : List ℕ}
    {fs : List Form} {vs : List Value} (hnd : ds.Nodup) (hf : ds.length = fs.length)
    (hv : ds.length = vs.length) (hT : T.Holds x w l val)
    (hsub : Table.sub T' T (ds.zip fs) = true)
    (hnew : ∀ r (h : r < ds.length), (fs[r]'(hf ▸ h)).Holds x w l (vs[r]'(hv ▸ h))) :
    T'.Holds x w l (valueEx val (ds.zip vs)) := by
  intro p hp
  have hkeys : (ds.zip vs).map Prod.fst = ds := List.map_fst_zip (by omega)
  rcases Table.mem_of_sub hsub p hp with h | ⟨hk, h⟩
  · obtain ⟨r, hr, hpr⟩ := List.getElem_of_mem h
    rw [List.length_zip, ← hf, Nat.min_self] at hr
    have hp' : p = (ds[r], fs[r]'(hf ▸ hr)) := by rw [← hpr, List.getElem_zip]
    have hq : (ds[r], vs[r]'(hv ▸ hr)) ∈ ds.zip vs := by
      rw [← List.getElem_zip (i := r) (h := by rw [List.length_zip, ← hv, Nat.min_self]; exact hr)]
      exact List.getElem_mem _
    have hval := Thread.valueEx_of_mem (by rw [hkeys]; exact hnd) hq val
    rw [hp']
    change (fs[r]'(hf ▸ hr)).Holds x w l (valueEx val (ds.zip vs) ds[r])
    rw [hval]
    exact hnew r hr
  · have hk' : p.1 ∉ (ds.zip vs).map Prod.fst := by
      rw [hkeys]
      rwa [List.map_fst_zip (by omega)] at hk
    rw [Thread.valueEx_of_not_mem hk']
    exact hT p h

/-- A table on a smaller table: the same slot file. -/
theorem Table.weaken {T T' : Table} {x : Inputs} {w l : ℕ} {val : ℕ → Value}
    (hT : T.Holds x w l val) (hsub : Table.sub T' T [] = true) : T'.Holds x w l val := by
  intro p hp
  rcases Table.mem_of_sub hsub p hp with h | h
  · cases h
  · exact hT p h.2

end

end PTX.Kernels.FlashKdaFwd.Proof.Values

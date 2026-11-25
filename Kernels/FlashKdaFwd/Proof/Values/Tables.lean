-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Forms
public import Kernels.FlashKdaFwd.Proof.Thread.Base

@[expose] public section

/-!
# Register tables across runs of scalar instructions, and across tiles

`Forms.lean` moves a register table (`Table`: the data registers live at a program point, each
with its form) across one event. This file adds what the later phases of a tile need.

* **Runs.** After some events the thread machine executes a *run*: a straight piece of scalar
  instructions that it evaluates in one go. The generated run gives the registers it leaves as
  a list `F` of pairs (register, value) (`Run.r<pc>_facts<k>`), computed from the register file
  `V` before the run. `Table.Outs x w l F O` says the listed values satisfy the forms of the
  table `O`; `Table.run_step` then gives the table after the run from the table `M` before it:
  each entry of the new table is an output of the run or an entry of `M` at a register the run
  does not list (`Table.covers`: every listed register has an entry in `O`).
  `Table.holds_valueOf` reads the inputs of a run off a table: the machine's register file
  `valueOf d` agrees with the data slots `d.x` on *opaque* registers (`isOpaque`: the registers
  whose values the machine does not track as integers).
* **`Table.frame`**: a table is untouched by writes to registers it does not list.
* **`AllOf`**: a statement for each element of a literal list, as a conjunction that a generated
  proof builds element by element.
* **The next tile.** `Chain xs tiles` says the FP32 state that tile `b + 1` starts from is the
  state tile `b` ends with (`Math.Fragments.stateAfter`), for the tiles `b < tiles`; then a
  carry register that holds its updated entry for tile `b` (form `regC (nextState …)`) holds its
  carry for tile `b + 1` (form `carry …`): `carry_next`, and `Table.next_holds` for a whole table
  (`Table.nextOf` is the Boolean check that the second table is the first with the forms
  renamed).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments

noncomputable section

/-! ## The outputs of a run -/

/-- The run's result list `F` gives each register of `O` a value that satisfies its form. -/
def Table.Outs (x : Inputs) (w l : ℕ) (F : List (ℕ × Value)) : Table → Prop
  | [] => True
  | p :: O => (∃ v, F.lookup p.1 = some v ∧ p.2.Holds x w l v) ∧ Table.Outs x w l F O

theorem Table.Outs.mem {x : Inputs} {w l : ℕ} {F : List (ℕ × Value)} :
    ∀ {O : Table}, Table.Outs x w l F O →
      ∀ p ∈ O, ∃ v, F.lookup p.1 = some v ∧ p.2.Holds x w l v
  | [], _, p, hp => by cases hp
  | q :: O, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact h.1
    · exact Table.Outs.mem h.2 p hp'

theorem Table.Outs.nil {x : Inputs} {w l : ℕ} {F : List (ℕ × Value)} : Table.Outs x w l F [] :=
  trivial

theorem Table.Outs.cons {x : Inputs} {w l : ℕ} {F : List (ℕ × Value)} {r : ℕ} {f : Form}
    {O : Table} {v : Value} (hv : F.lookup r = some v) (hf : f.Holds x w l v)
    (hO : Table.Outs x w l F O) : Table.Outs x w l F ((r, f) :: O) :=
  ⟨⟨v, hv, hf⟩, hO⟩

/-- Every register of `ks` has an entry in `O`. -/
def Table.covers (O : Table) (ks : List ℕ) : Bool := ks.all fun r => O.any fun q => q.1 == r

/-- **A table across a run.** `val` is the slot file before the run (it satisfies `M`), `F` the
run's result list, whose registers are `ks`. The table `T'` holds afterwards when each of its
entries is an output of the run (an entry of `O`) or an entry of `M` at a register that is not
in `O`, and `O` covers `ks`. -/
theorem Table.run_step {T' M O : Table} {x : Inputs} {w l : ℕ} {val : ℕ → Value}
    {F : List (ℕ × Value)} (hM : M.Holds x w l val) (hO : Table.Outs x w l F O) {ks : List ℕ}
    (hks : F.map Prod.fst = ks) (hcov : O.covers ks = true)
    (hsub : Table.sub T' M O = true) : T'.Holds x w l (valueEx val F) := by
  intro p hp
  rcases Table.mem_of_sub hsub p hp with h | ⟨hk, h⟩
  · obtain ⟨v, hv, hf⟩ := hO.mem p h
    have hval : valueEx val F p.1 = v := by simp only [valueEx, hv, Option.getD_some]
    rw [hval]
    exact hf
  · have hk' : p.1 ∉ F.map Prod.fst := by
      rw [hks]
      intro hm
      obtain ⟨q, hq, hq1⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcov _ hm)
      exact hk (List.mem_map.mpr ⟨q, hq, by simpa using hq1⟩)
    rw [Thread.valueEx_of_not_mem hk']
    exact hM p h

/-- Every entry of `I` is an entry of `M` at an opaque register. -/
def Table.readable (I M : Table) : Bool := I.all fun p => M.has p.1 p.2 && isOpaque p.1

/-- **The inputs of a run.** The register file of a state whose slots satisfy `M` satisfies
every table of opaque registers of `M`. -/
theorem Table.holds_valueOf {I M : Table} {x : Inputs} {w l : ℕ} {d : D}
    (hM : M.Holds x w l d.x) (hI : I.readable M = true) : I.Holds x w l (valueOf d) := by
  intro p hp
  have h := List.all_eq_true.mp hI p hp
  simp only [Bool.and_eq_true] at h
  rw [valueOf_opaque h.2]
  exact hM.get h.1

/-- **A table is untouched by writes to other registers.** -/
theorem Table.frame {T : Table} {x : Inputs} {w l : ℕ} {val : ℕ → Value}
    {E : List (ℕ × Value)} (hT : T.Holds x w l val) {ks : List ℕ} (hks : E.map Prod.fst = ks)
    (hd : (T.all fun p => !ks.contains p.1) = true) : T.Holds x w l (valueEx val E) := by
  intro p hp
  have h := List.all_eq_true.mp hd p hp
  have hk : p.1 ∉ E.map Prod.fst := by
    rw [hks]
    simpa using h
  rw [Thread.valueEx_of_not_mem hk]
  exact hT p hp

/-! ## A statement for each element of a literal list -/

/-- `P` holds of every element of the list, as a conjunction. -/
def AllOf {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: as => P a ∧ AllOf P as

theorem AllOf.mem {α : Type} {P : α → Prop} : ∀ {as : List α}, AllOf P as → ∀ a ∈ as, P a
  | [], _, a, ha => by cases ha
  | b :: as, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h.1
    · exact AllOf.mem h.2 a ha'

/-! ## The carries of the next tile -/

/-- **The tiles form a chain**: the FP32 state that tile `b + 1` starts from is the state that
tile `b` ends with, for the 128 key features and the 128 value channels and each of the `tiles`
tiles of the sequence (the family's entry number `tiles` is then the final state). -/
def Chain (xs : ℕ → Inputs) (tiles : ℕ) : Prop :=
  ∀ b < tiles, ∀ k ch, k < 128 → ch < 128 → (xs (b + 1)).carry k ch = stateAfter (xs b) k ch

/-- A carry register after its fused multiply-add of the tile holds its carry of the next
tile. -/
theorem carry_next {x x' : Inputs}
    (h : ∀ k ch, k < 128 → ch < 128 → x'.carry k ch = stateAfter x k ch) {w l m bi q r : ℕ}
    (hw : w < 4) (hl : l < 32) (hm : m < 8) (hbi : bi < 2) (hq : q < 2) (hr : r < 4)
    {v : Value} (hv : (Form.regC (.nextState bi q m) r).Holds x w l v) :
    (Form.carry m bi q r).Holds x' w l v := by
  have e : v = Value.float .f32
      (nextState x (halfBase w bi q) m (cRow l r) (cCol l r)) := hv
  have hc : cRow l r < 16 := by unfold cRow; omega
  have hcc : cCol l r < 8 := by unfold cCol; omega
  have hb : halfBase w bi q = 16 * (2 * w + bi) + 8 * q := rfl
  have key := h (16 * m + cRow l r) (halfBase w bi q + cCol l r) (by omega) (by rw [hb]; omega)
  rw [stateAfter, show 8 * ((halfBase w bi q + cCol l r) / 8) = halfBase w bi q by rw [hb]; omega,
    show (16 * m + cRow l r) / 16 = m by omega,
    show (16 * m + cRow l r) % 16 = cRow l r by omega,
    show (halfBase w bi q + cCol l r) % 8 = cCol l r by rw [hb]; omega] at key
  change v = _
  rw [key]
  exact e

/-- The form of a register at the start of the next tile, for the registers that live across
the tile boundary: an updated carry becomes the carry of the next tile (with the index bounds
of a real carry register). -/
def Form.next : Form → Option Form
  | .regC (.nextState bi q m) r =>
    if m < 8 ∧ bi < 2 ∧ q < 2 ∧ r < 4 then some (.carry m bi q r) else none
  | _ => none

/-- Every entry of `T0` is an entry of `T` with the form of the next tile. -/
def Table.nextOf (T T0 : Table) : Bool :=
  T0.all fun p => T.any fun q => q.1 == p.1 && decide (q.2.next = some p.2)

/-- **A table at the start of the next tile.** -/
theorem Table.next_holds {T T0 : Table} {x x' : Inputs} {w l : ℕ} {val : ℕ → Value}
    (h : ∀ k ch, k < 128 → ch < 128 → x'.carry k ch = stateAfter x k ch) (hw : w < 4)
    (hl : l < 32) (hT : T.Holds x w l val) (hn : T.nextOf T0 = true) : T0.Holds x' w l val := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := List.any_eq_true.mp (List.all_eq_true.mp hn p hp)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hqp
  have hv := hT q hq
  rw [hqp.1] at hv
  obtain ⟨r, f⟩ := p
  obtain ⟨r', f'⟩ := q
  simp only at hqp hv ⊢
  cases f' with
  | regC M c =>
    cases M with
    | nextState bi q' m =>
      simp only [Form.next] at hqp
      split_ifs at hqp with hb
      · have e := Option.some.inj hqp.2
        rw [← e]
        exact carry_next h hw hl hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hv
      · exact hqp.2.elim
    | _ => simp [Form.next] at hqp
  | _ => simp [Form.next] at hqp

end

end PTX.Kernels.FlashKdaFwd.Proof.Values

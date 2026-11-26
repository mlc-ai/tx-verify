-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.NoUb
public import Kernels.FlashKdaFwd.Proof.Ref.Swizzle

@[expose] public section

/-!
# Bridges to the value induction of the tile loop and to the reference layer

* `carriesHold_iff_holds`: the predicate `CarriesHold S tid val` of this directory ("the 128
  carry registers hold the state `S`") is the invariant of the tile loop at the first matrix
  instruction of a tile, `(tableAt 0).Holds x w l val` (`Proof/Values/Forms.lean`,
  `Contract.lean`), for arrays `x` whose carry is `S` (`x.carry k ch = S ch k`: the tile loop
  indexes the state by key feature first), warp `w = tid / 32` and lane `l = tid % 32`. So
  `carries_initial` is the base case `Val` at ordinal 0 of tile 0 up to the sites between the
  proxy fence 1401 and the first `ldmatrix`, and `FinalCarries` is the invariant at ordinal 0
  after the last tile, carried to the first final store.
  It rests on one evaluated check: the table of ordinal 0 lists exactly the carry registers of
  `Gen.carryTable`, each with the form `carry m bi q r` of its row (`tableAt_zero`).
* `swzAddr_eq_swzAbs`: the swizzle of this directory is the reference layer's `Ref.swzAbs`
  (`Proof/Ref/Swizzle.lean`), by definition.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Flow PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Math.Fragments (Inputs halfBase)

noncomputable section

/-- The swizzle of the generic pointers is the reference layer's. -/
theorem swzAddr_eq_swzAbs : swzAddr = Ref.swzAbs := rfl

/-- The carries with their forms, in the order of `Gen.carryTable`. -/
def carryForms : Table :=
  Gen.carryTable.map fun p => (p.1, Form.carry p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1)

/-- **The table of the tile loop at ordinal 0 is the table of the carries** (as sets). -/
theorem tableAt_zero : ((tableAt 0).all fun p => carryForms.contains p) = true ∧
    (carryForms.all fun p => (tableAt 0).contains p) = true := by
  decide +kernel

theorem carryRow_mem {j : ℕ} (hj : j < 128) : carryRow j ∈ Gen.carryTable := by
  unfold carryRow
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [carryTable_length]; exact hj), Option.getD_some]
  exact List.getElem_mem _

theorem exists_carryRow {q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hq : q ∈ Gen.carryTable) :
    ∃ j < 128, carryRow j = q := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  refine ⟨j, carryTable_length ▸ hj, ?_⟩
  unfold carryRow
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- **`CarriesHold` is the invariant of the tile loop at ordinal 0.** -/
theorem carriesHold_iff_holds {S : State} {tid : ℕ} {val : ℕ → Value} (ht : tid < 128)
    {x : Inputs}
    (hx : ∀ k ch (hk : k < 128) (hch : ch < 128), x.carry k ch = S ⟨ch, hch⟩ ⟨k, hk⟩) :
    CarriesHold S tid val ↔ (tableAt 0).Holds x (tid / 32) (tid % 32) val := by
  have hval : ∀ j < 128, x.carry (carryKey j tid) (carryChan j tid) =
      entry S (carryElem j tid) := fun j hj => by
    rw [hx _ _ (carryKey_lt hj) (carryChan_lt hj ht)]
    exact (entry_elemOf S ⟨_, carryChan_lt hj ht⟩ ⟨_, carryKey_lt hj⟩).symm
  constructor
  · intro h p hp
    have hp' : p ∈ carryForms := by
      simpa using List.all_eq_true.mp tableAt_zero.1 p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    obtain ⟨j, hj, rfl⟩ := exists_carryRow hq
    show val (carryReg j) = .float .f32 (x.carry (carryKey j tid) (carryChan j tid))
    rw [h j hj, hval j hj]
  · intro h j hj
    have hm : (carryReg j, Form.carry (carryRow j).2.1 (carryRow j).2.2.1 (carryRow j).2.2.2.1
        (carryRow j).2.2.2.2.1) ∈ tableAt 0 := by
      have : (carryReg j, Form.carry (carryRow j).2.1 (carryRow j).2.2.1 (carryRow j).2.2.2.1
          (carryRow j).2.2.2.2.1) ∈ carryForms :=
        List.mem_map.mpr ⟨carryRow j, carryRow_mem hj, rfl⟩
      simpa using List.all_eq_true.mp tableAt_zero.2 _ this
    have h1 : val (carryReg j) =
        .float .f32 (x.carry (carryKey j tid) (carryChan j tid)) := h _ hm
    rw [h1, hval j hj]

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends

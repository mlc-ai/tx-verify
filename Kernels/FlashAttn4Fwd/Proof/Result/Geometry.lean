-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Result
public import Lemmas.Tensor.TensorAddress
public import Lemmas.Arith.MixedRadix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The bytes of an output tensor store

A tensor store of half `hh` of stage `st` of an item (`oSpec`) has the slots `x < 64`, `y < 128`,
`k < 2` (`oSpec_slot`). Slot `(x, y, k)` reads the staging byte `stageLoc` (`oSpec_readLoc`) and,
when the item exists, writes byte `k` of O's element `(row tileRow + y, column 64 hh + x)` of
the item's batch and head (`oSpec_writeLoc`). An element byte of O lies in O (`element_in`), and
two element bytes in range are one byte only when their indices agree (`element_inj`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX TensorDescriptor

noncomputable section

namespace Result

variable {P : Params} {L : Launch}

/-- **Two element bytes in range are one byte only when their indices agree.** -/
theorem element_inj {base rows b1 h1 r1 d1 k1 b2 h2 r2 d2 k2 : Nat} (hh1 : h1 < P.h)
    (hr1 : r1 < rows) (hd1 : d1 < 128) (hk1 : k1 < 2) (hh2 : h2 < P.h) (hr2 : r2 < rows)
    (hd2 : d2 < 128) (hk2 : k2 < 2)
    (he : (elementLoc P base rows b1 h1 r1 d1).at k1 = (elementLoc P base rows b2 h2 r2 d2).at k2) :
    b1 = b2 ∧ h1 = h2 ∧ r1 = r2 ∧ d1 = d2 ∧ k1 = k2 := by
  simp only [elementLoc, Loc.at, Loc.mk.injEq, true_and] at he
  generalize hq1 : (b1 * rows + r1) * P.h + h1 = q1 at he
  generalize hq2 : (b2 * rows + r2) * P.h + h2 = q2 at he
  obtain ⟨ha, rfl⟩ := Nat.digits_of_eq (n := 2) hk1 hk2 (by omega : (q1 * 128 + d1) * 2 + k1 =
    (q2 * 128 + d2) * 2 + k2)
  obtain ⟨hq, rfl⟩ := Nat.digits_of_eq hd1 hd2 ha
  subst hq
  obtain ⟨hr, rfl⟩ := Nat.digits_of_eq hh1 hh2 (hq1.trans hq2.symm)
  obtain ⟨rfl, rfl⟩ := Nat.digits_of_eq hr1 hr2 hr
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **An element byte of O lies in O.** -/
theorem element_in {batch head row d k : Nat} (hb : batch < P.b) (hh : head < P.h)
    (hr : row < P.sq) (hd : d < 128) (hk : k < 2) :
    P.oBase ≤ ((elementLoc P P.oBase P.sq batch head row d).at k).addr ∧
      ((elementLoc P P.oBase P.sq batch head row d).at k).addr < P.oBase + tensorBytes P P.sq := by
  simp only [elementLoc, Loc.at, tensorBytes]
  have h1 : ((batch * P.sq + row) * P.h + head) * 128 + d < P.b * P.sq * P.h * 128 := by
    have e1 : batch * P.sq + row < P.b * P.sq := by
      calc batch * P.sq + row < batch * P.sq + P.sq := by omega
        _ = (batch + 1) * P.sq := by ring
        _ ≤ P.b * P.sq := Nat.mul_le_mul_right _ hb
    have e2 : (batch * P.sq + row) * P.h + head < P.b * P.sq * P.h := by
      calc (batch * P.sq + row) * P.h + head < (batch * P.sq + row) * P.h + P.h := by omega
        _ = (batch * P.sq + row + 1) * P.h := by ring
        _ ≤ P.b * P.sq * P.h := Nat.mul_le_mul_right _ e1
    omega
  have e3 : 256 * P.b * P.h * P.sq = P.b * P.sq * P.h * 128 * 2 := by ring
  omega

/-- A store's box has 64 columns. -/
theorem oSpec_count {g j st hh : Nat} :
    TensorTile.count (oSpec P L g j st hh).descriptor.box 0 = 64 := by
  simp [TensorTile.count, TensorTile.step, oSpec, FlashAttn4Fwd.mapO, encodeTiled]

/-- A store's box has 128 rows. -/
theorem oSpec_rows {g j st hh : Nat} :
    TensorTile.rows (oSpec P L g j st hh).descriptor.box = 128 := by
  simp [TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step, oSpec,
    FlashAttn4Fwd.mapO, encodeTiled]

/-- The element indices of column `x` of row `y` of the O map's box. -/
theorem oBox_indexOf {x y : Nat} (hy : y < 128) :
    TensorTile.indexOf oBox x y = ![x, y, 0, 0] := by
  funext a
  have : y / 128 = 0 := Nat.div_eq_of_lt hy
  fin_cases a <;> simp [TensorTile.indexOf, TensorTile.unflatten, TensorTile.count,
    TensorTile.step, oBox, Nat.mod_eq_of_lt hy, this] <;> rfl

/-- The slot of a store's selected byte `(x, y, k)`, which is in range. -/
theorem oSpec_slotAt {g j st hh x y k : Nat} (hx : x < 64) (hy : y < 128) (hk : k < 2) :
    TensorTransfer.slotAt (oSpec P L g j st hh).descriptor x y k =
      some ⟨⟨x, by rw [oSpec_count]; exact hx⟩, ⟨y, by rw [oSpec_rows]; exact hy⟩, ⟨k, hk⟩⟩ := by
  unfold TensorTransfer.slotAt
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd hk h3
  · exact absurd (by rw [oSpec_rows]; exact hy) h2
  · exact absurd (by rw [oSpec_count]; exact hx) h1

/-- The tensor coordinate of element `(x, y)` of a store's box. -/
theorem oOrigin_coord {g j st hh x y : Nat} (hy : y < 128) :
    TensorTile.coord oBox (oOrigin L g j st hh) (TensorTile.indexOf oBox x y) =
      ![((64 * hh + x : Nat) : Int), ((tileRow L g j st + y : Nat) : Int),
        ((tileHead L g j : Nat) : Int), ((tileBatch L g j : Nat) : Int)] := by
  rw [oBox_indexOf hy]
  funext a
  fin_cases a <;> simp [TensorTile.coord, TensorTile.step, oBox, oOrigin]

/-- The tensor coordinate of a store's slot `(x, y, k)`. -/
theorem oSpec_coord {g j st hh x y k : Nat} (hx : x < 64) (hy : y < 128) (hk : k < 2) :
    TensorTransfer.coord (oSpec P L g j st hh).descriptor (oSpec P L g j st hh).origin
        (oSpec P L g j st hh).rows
        ⟨⟨x, by rw [oSpec_count]; exact hx⟩, ⟨y, by rw [oSpec_rows]; exact hy⟩, ⟨k, hk⟩⟩ =
      ![((64 * hh + x : Nat) : Int), ((tileRow L g j st + y : Nat) : Int),
        ((tileHead L g j : Nat) : Int), ((tileBatch L g j : Nat) : Int)] := by
  simp only [TensorTransfer.coord, TensorTransfer.index]
  exact oOrigin_coord hy

/-- The O map's address of byte `k` of element `(batch, head, row, d)` in range. -/
theorem o_lookup {batch head row d k : Nat} (hb : batch < P.b) (hh : head < P.h)
    (hr : row < P.sq) (hd : d < 128) (hk : k < 2) :
    TensorAddress.lookup (geometry (FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass))
      ![((d : Nat) : Int), ((row : Nat) : Int), ((head : Nat) : Int), ((batch : Nat) : Int)] k =
      some ((elementLoc P P.oBase P.sq batch head row d).at k).addr := by
  apply (TensorAddress.lookup_some_iff _ _ _ _).mpr
  refine ⟨fun axis => ?_, hk, ?_⟩
  · fin_cases axis <;> simp [geometry, FlashAttn4Fwd.mapO, encodeTiled] <;> omega
  · unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_four]
    show _ = P.oBase + ((d : Int).toNat * 2 + (row : Int).toNat * (256 * P.h) +
      (head : Int).toNat * 256 + (batch : Int).toNat * (256 * P.h * P.sq)) + k
    simp only [Int.toNat_natCast, elementLoc, Loc.at]
    ring

/-- **The global byte a store's slot writes**: byte `k` of O's element `(tileRow + y, 64 hh + x)`
of the item's batch and head, when they are in range. -/
theorem oSpec_writeLoc {g j st hh x y k : Nat} (hx : x < 64) (hy : y < 128) (hk : k < 2)
    (hhh : hh < 2) (hrow : tileRow L g j st + y < P.sq) (hhead : tileHead L g j < P.h)
    (hbatch : tileBatch L g j < P.b) :
    TensorStore.writeLoc (oSpec P L g j st hh) x y k = some ((elementLoc P P.oBase P.sq
      (tileBatch L g j) (tileHead L g j) (tileRow L g j st + y) (64 * hh + x)).at k) := by
  unfold TensorStore.writeLoc
  rw [oSpec_slotAt hx hy hk]
  simp only [Option.bind_some, TensorStore.destination, TensorBox.globalAddress,
    TensorTransfer.globalAddress]
  erw [oSpec_coord hx hy hk]
  erw [o_lookup hbatch hhead hrow (by omega) hk]
  rfl

/-- **A store's selected bytes** are `x < 64`, `y < 128`, `k < 2`. -/
theorem oSpec_slot {g j st hh x y k : Nat} {l : Loc}
    (hl : TensorStore.writeLoc (oSpec P L g j st hh) x y k = some l) :
    x < 64 ∧ y < 128 ∧ k < 2 := by
  unfold TensorStore.writeLoc at hl
  obtain ⟨slot, hs, -⟩ := Option.bind_eq_some_iff.mp hl
  unfold TensorTransfer.slotAt at hs
  split_ifs at hs with h1 h2 h3
  rw [oSpec_count] at h1
  rw [oSpec_rows] at h2
  exact ⟨h1, h2, h3⟩

/-- **The staging byte a store's slot reads.** -/
theorem oSpec_readLoc {g j st hh x y k : Nat} (hx : x < 64) (hy : y < 128) (hk : k < 2) :
    TensorStore.readLoc (oSpec P L g j st hh) x y k =
      some (stageLoc L (ctaOf L g) st hh x y k) := by
  unfold TensorStore.readLoc
  rw [oSpec_slotAt hx hy hk]
  rfl

end Result

end

end PTX.Kernels.FlashAttn4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

open TensorDescriptor
noncomputable section

/-- Coordinates used by the rank-four output map after selecting one query sequence. -/
def oCoordinate (p : Params) (batch head row d : Nat) : Fin 4 → Int :=
  ![(d : Int), (((2 ^ 30 - p.qLength batch : Nat) + row : Nat) : Int),
    (head : Int), (p.qOffset (batch + 1) : Int)]

theorem Pre.qOffset_mono {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b b' : Nat} (hle : b ≤ b') (hb : b' ≤ p.batch) : p.qOffset b ≤ p.qOffset b' := by
  have h (n : Nat) (hn : b + n ≤ p.batch) : p.qOffset b ≤ p.qOffset (b + n) := by
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih =>
      exact Nat.le_trans (ih (by omega)) (hp.lengths (b + n) (by omega)).1
  simpa only [Nat.add_sub_of_le hle] using h (b' - b) (by omega)

theorem Pre.qOffset_le_total {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b : Nat} (hb : b ≤ p.batch) : p.qOffset b ≤ p.totalQ :=
  hp.qOffset_mono hb (by rfl)

theorem Pre.qLength_fits {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b : Nat} (hb : b < p.batch) : p.qLength b ≤ 2 ^ 30 := by
  have hEnd := hp.qOffset_le_total (b := b + 1) (by omega)
  have hTotal := hp.shape.2.2.2.2
  unfold Params.qLength
  omega

/-- A ragged-map coordinate in a valid query row reaches the ordinary packed O byte. -/
theorem outputLookup (p : Params) {batch head row d k : Nat}
    (hBase : 2 ^ 30 * (512 * p.heads) ≤ p.oBase)
    (hOffsets : p.qOffset batch ≤ p.qOffset (batch + 1))
    (hLength : p.qLength batch ≤ 2 ^ 30)
    (hEnd : p.qOffset (batch + 1) < 2 ^ 31 - 1)
    (hHead : head < p.heads) (hRow : row < p.qLength batch) (hD : d < 128) (hK : k < 4) :
    TensorAddress.lookup (geometry p.oMap) (oCoordinate p batch head row d) k =
      some ((p.oLoc (p.qOffset batch + row) head d).at k).addr := by
  have hIn : TensorAddress.InBounds (geometry p.oMap) (oCoordinate p batch head row d) := by
    intro axis
    fin_cases axis <;> simp [geometry, Params.oMap, oCoordinate] <;> omega
  unfold TensorAddress.lookup
  rw [ite_eq_left ⟨hIn, hK⟩]
  congr 1
  unfold TensorAddress.byteAddress
  rw [Fin.sum_univ_four]
  let stride := 512 * p.heads
  let shift := 2 ^ 30 - p.qLength batch + row
  let finish := p.qOffset (batch + 1)
  have hJoin : shift + finish = 2 ^ 30 + (p.qOffset batch + row) := by
    unfold shift finish Params.qLength at *
    omega
  change p.oBase - 2 ^ 30 * stride +
      ((d : Int).toNat * 4 + (shift : Int).toNat * stride +
        (head : Int).toNat * 512 + (finish : Int).toNat * stride) + k =
    p.oBase + 4 * (((p.qOffset batch + row) * p.heads + head) * 128 + d) + k
  simp only [Int.toNat_natCast]
  calc
    _ = (p.oBase - 2 ^ 30 * stride) + (shift + finish) * stride + head * 512 + d * 4 + k := by
      ring
    _ = p.oBase + (p.qOffset batch + row) * stride + head * 512 + d * 4 + k := by
      rw [hJoin, Nat.add_mul, ← Nat.add_assoc, Nat.sub_add_cancel hBase]
    _ = _ := by unfold stride; ring

/-- The shifted row reaches the ragged dimension's upper extent exactly at the end of a request.
A tail store has no destination, even when the next request has packed output rows. -/
theorem outputTailLookup (p : Params) {batch head row d k : Nat}
    (hLength : p.qLength batch ≤ 2 ^ 30) (hRow : p.qLength batch ≤ row) :
    TensorAddress.lookup (geometry p.oMap) (oCoordinate p batch head row d) k = none := by
  unfold TensorAddress.lookup
  apply ite_eq_right
  intro h
  have hAxis := (h.1 (1 : Fin 4)).2
  simp [geometry, Params.oMap, oCoordinate] at hAxis
  omega


theorem outputLookup_of_pre {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {batch head row d k : Nat} (hb : batch < p.batch)
    (hh : head < p.heads) (hr : row < p.qLength batch) (hd : d < 128) (hk : k < 4) :
    TensorAddress.lookup (geometry p.oMap) (oCoordinate p batch head row d) k =
      some ((p.oLoc (p.qOffset batch + row) head d).at k).addr := by
  have hEnd := hp.qOffset_le_total (b := batch + 1) (by omega)
  have hTotal := hp.shape.2.2.2.2
  exact outputLookup p hp.raggedBase (hp.lengths batch hb).1 (hp.qLength_fits hb)
    (by omega) hh hr hd hk

theorem outputTailLookup_of_pre {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {batch head row d k : Nat} (hb : batch < p.batch)
    (hr : p.qLength batch ≤ row) :
    TensorAddress.lookup (geometry p.oMap) (oCoordinate p batch head row d) k = none :=
  outputTailLookup p (hp.qLength_fits hb) hr

end
end PTX.Kernels.TmlFa4Fwd

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmStgE
public import Kernels.InklingRelDecode.Proof.Thread.SmStg

@[expose] public section

/-! # The two lanes of a row: what the exchanges need from the partner

The 128 columns of a row of the score tile are split between two threads, the lane and the lane
`^ 16` (`half`). The row's maximum and sum are exchanged by two shuffles (`shfl5`: the maximum,
`shfl6`: the sum of the probabilities). The thread's step lemmas (`step_shfl5`, `step_shfl6`)
speak only about the thread's own state and the word the shuffle returned; what the word is, is a
fact about the partner. This file states the facts, as premises of an abstract kind (a state of
the partner), and proves what follows from them for one thread:

* `Peer d dp`: the partner's state `dp` has the same entry numbers (the scale) and the same running
  maximum as `d`. It is the only premise about the partner's history; the protocol layer supplies
  it (both lanes run the same loop and the same exchanges: the running maximum after block `i` is
  the same for both because both took the maximum over the same row).
* the word the maximum's shuffle returns is the partner's maximum, `erealValue .f32 dp.ownE`;
  the sum's shuffle returns the partner's sum, read as the number `y` (`.float .f32 y`).

From these: both lanes take the same decision and the same `m_use` (`decision_peer`); each lane's
maximum is the block maximum of its visible scores (`ownE_eq`), so the lanes' maxima are `RowOf`
(`PeerExchange.rowOf`); and the row sum the thread records is the sum of the probabilities of the
visible scores of both lanes (`PeerExchange.rs_eq`, the `hrs` of `SmStg.upd_eq_step_v`: a masked
column has probability `0`, so the sum over the 64 columns is the sum over the visible ones,
`sumP_afterMax`). `PeerExchange` bundles the premises the protocol layer supplies. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Softmax
open Classical

noncomputable section
set_option maxRecDepth 100000

/-! ### The partner -/

/-- The partner lane's state has the thread's entry numbers and running maximum. -/
structure Peer (d dp : D) : Prop where
  e : dp.e = d.e
  m : dp.m = d.m

/-- The extended real an extended real that is not `+inf` is the value of. -/
theorem eOf_erealValue {E : EReal} (h : E ≠ ⊤) : eOf (erealValue .f32 E) = E := by
  induction E using EReal.rec with
  | bot =>
    rw [erealValue_bot']
    rfl
  | coe x => rw [erealValue_coe]; rfl
  | top => exact absurd rfl h

theorem ownE_ne_top (d : D) (h : ∀ k < 64, ScoreWord (d.stg.fsv k).1) : d.ownE ≠ ⊤ :=
  (cmaxW_lt_top h fullMask).ne

/-! ### The same decision in both lanes -/

theorem mnE_peer {d dp : D} (hp : Peer d dp) :
    dp.mnE d.ownE = d.mnE dp.ownE := by
  unfold D.mnE D.mE
  rw [hp.m]
  exact max_right_comm _ _ _

theorem aLog_peer {d dp : D} (hp : Peer d dp) : dp.aLog d.ownE = d.aLog dp.ownE := by
  unfold D.aLog D.mE
  rw [hp.e, hp.m, mnE_peer hp]

/-- **Both lanes take the same decision**: `Keep`, `m_use`, `alpha`. -/
theorem decision_peer {d dp : D} (hp : Peer d dp) :
    dp.keepB d.ownE = d.keepB dp.ownE ∧ dp.mUse d.ownE = d.mUse dp.ownE ∧
      dp.alV d.ownE = d.alV dp.ownE ∧ dp.alR d.ownE = d.alR dp.ownE := by
  have h1 := aLog_peer hp
  have h2 := mnE_peer hp
  have h3 : dp.mE = d.mE := by unfold D.mE; rw [hp.m]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold D.keepB; rw [h1]
  · unfold D.mUse; rw [h1, h2, h3]
  · unfold D.alV; rw [h1]
  · unfold D.alR; rw [h1]

/-! ### The sum over the 64 columns is the sum over the visible ones -/

/-- The scores of the thread's visible columns (the `.f32` numbers among its 64 score words), in
column order. -/
def D.ownScores (d : D) : List ℝ :=
  (List.range 64).filterMap fun k => match (d.stg.fsv k).1 with
    | .float _ x => some x
    | _ => none

theorem sum_pOfV (sl mu : ℝ) (w : Nat → Value) : ∀ n,
    ((List.range n).map fun k => pOfV sl mu (w k)).sum =
      (((List.range n).filterMap fun k => match w k with
        | .float _ x => some x
        | _ => none).map fun x => (2 : ℝ) ^ (x * sl + mu * (-sl))).sum := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.filterMap_append, List.map_append,
      List.sum_append, ih]
    congr 1
    cases hw : w n <;> simp [hw, pOfV]

/-- **`hrs`, the thread's part**: the sum of the 64 probabilities after the row maximum's shuffle
is the sum over the visible scores. -/
theorem sumP_afterMax (d : D) (rv : Value) :
    (d.afterMax rv).sumP =
      (d.ownScores.map fun x =>
        (2 : ℝ) ^ (x * slOf d.e + d.mUse (eOf rv) * (-slOf d.e))).sum := by
  unfold D.sumP D.afterMax D.ownScores
  exact sum_pOfV (slOf d.e) (d.mUse (eOf rv)) (fun k => (d.stg.fsv k).1) 64

/-! ### The maximum of the 64 columns is the block maximum of the visible scores -/

theorem foldr_visW (w : Nat → Value) : ∀ l : List Nat,
    l.foldr (fun k acc => max (eOf (w k)) acc) ⊥ =
      (l.filterMap fun k => match w k with | .float _ x => some x | _ => none).foldr
        (fun (x : ℝ) (acc : EReal) => max (x : EReal) acc) ⊥
  | [] => rfl
  | k :: l => by
    rw [List.foldr_cons, foldr_visW w l, List.filterMap_cons]
    unfold eOf
    cases hk : w k <;> simp [List.foldr_cons]

/-- **The thread's maximum is the block maximum of its visible scores**, for every block whose
scores are the thread's visible ones. -/
theorem ownE_eq (d : D) {blk : List (ℝ × ℝ)} (h : blk.map Prod.fst = d.ownScores) :
    d.ownE = Softmax.blockMax blk := by
  rw [blockMax_eq, h]
  unfold D.ownE cmaxW D.ownScores
  have : (Finset.range 64).filter (fun k => fullMask.testBit k) = (List.range 64).toFinset := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, List.mem_range,
      fullMask, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    tauto
  rw [this, toFinset_sup_foldr, foldr_visW]

/-- **The row sum the thread records** (`D.afterSum`) is `SmStg.upd_eq_step_v`'s `hrs`: the sum
over the visible scores of the row's two halves (`bo` the thread's, `bp` the partner's), with the
exponent `sl * s - m_use * sl`.

The premises about the partner: it has the thread's entry numbers and running maximum (`hp`); the
word the maximum's shuffle returned is its maximum (`hrv`) and the one it received is the thread's;
the word the sum's shuffle returned is its sum of probabilities, computed with what it received
(`hy`); the score words of both are `f32` numbers or `-inf` (`hown`, `hdown`). -/
theorem rs_eq {d dp : D} {rv : Value} {y : ℝ} {bo bp : List (ℝ × ℝ)} (hp : Peer d dp)
    (hown : ∀ k < 64, ScoreWord (d.stg.fsv k).1) (hdown : ∀ k < 64, ScoreWord (dp.stg.fsv k).1)
    (hrv : rv = erealValue .f32 dp.ownE)
    (hy : y = (dp.afterMax (erealValue .f32 d.ownE)).sumP)
    (hrow : RowOf d rv bo bp) (hbo : bo.map Prod.fst = d.ownScores)
    (hbp : bp.map Prod.fst = dp.ownScores) :
    valFloat .f32 ((d.afterMax rv).afterSumR y).stg.rs =
      .ok (((bo ++ bp).map fun q => (2 : ℝ) ^ (slOf d.e * q.1 -
        (if Keep (alphaLog2 (slOf d.e) d.mE (max d.mE (blockMax (bo ++ bp)))) then d.mE.toReal
          else mSafe (max d.mE (blockMax (bo ++ bp)))) * slOf d.e)).sum) := by
  have hrv' : eOf rv = dp.ownE := by
    rw [hrv]
    exact eOf_erealValue (ownE_ne_top dp hdown)
  have hown' : eOf (erealValue .f32 d.ownE) = d.ownE := eOf_erealValue (ownE_ne_top d hown)
  have hmu' : dp.mUse (eOf (erealValue .f32 d.ownE)) = d.mUse (eOf rv) := by
    rw [hown', hrv']
    exact (decision_peer hp).2.1
  have hy' : y = (dp.ownScores.map fun x =>
      (2 : ℝ) ^ (x * slOf d.e + d.mUse (eOf rv) * (-slOf d.e))).sum := by
    rw [hy, sumP_afterMax, hmu', hp.e]
  have hmn := mnE_eq hrow
  have hmu : d.mUse (eOf rv) =
      if Keep (alphaLog2 (slOf d.e) d.mE (max d.mE (blockMax (bo ++ bp)))) then d.mE.toReal
        else mSafe (max d.mE (blockMax (bo ++ bp))) := by
    unfold D.mUse D.aLog
    rw [hmn]
  have hs := sumP_afterMax d rv
  have e1 : ((d.afterMax rv).afterSumR y).stg.rs =
      .float .f32 ((d.afterMax rv).sumP + y) := rfl
  have hmap : d.ownScores ++ dp.ownScores = (bo ++ bp).map Prod.fst := by
    rw [List.map_append, hbo, hbp]
  rw [e1, valFloat_float, hs, hy', ← List.sum_append, ← List.map_append, hmu, hmap, List.map_map]
  refine congrArg Except.ok (congrArg List.sum (List.map_congr_left fun q _ => ?_))
  simp only [Function.comp]
  congr 1
  ring

/-- **What the protocol layer supplies for one row's two exchanges**: the partner `dp` of the
thread `d`, the word `rv` the maximum's shuffle returned and the number `y` the sum's shuffle
returned. Every field is a statement about abstract states and values. -/
structure PeerExchange (d dp : D) (rv : Value) (y : ℝ) : Prop where
  peer : Peer d dp
  /-- The score words of both lanes are `f32` numbers or `-inf` (checked by `next shfl5`). -/
  own : ∀ k < 64, ScoreWord (d.stg.fsv k).1
  partner : ∀ k < 64, ScoreWord (dp.stg.fsv k).1
  /-- The maximum's shuffle returned the partner's maximum. -/
  maxW : rv = erealValue .f32 dp.ownE
  /-- The sum's shuffle returned the partner's sum, which it computed from the thread's maximum. -/
  sumW : y = (dp.afterMax (erealValue .f32 d.ownE)).sumP

/-- **The two lanes' maxima are the row's block**: the premises of `SmStg.RowOf`. -/
theorem PeerExchange.rowOf {d dp : D} {rv : Value} {y : ℝ} {bo bp : List (ℝ × ℝ)}
    (hx : PeerExchange d dp rv y) (hbo : bo.map Prod.fst = d.ownScores)
    (hbp : bp.map Prod.fst = dp.ownScores) : RowOf d rv bo bp where
  own := ownE_eq d hbo
  peer := by
    rw [hx.maxW, eOf_erealValue (ownE_ne_top dp hx.partner)]
    exact ownE_eq dp hbp

/-- `rs_eq` for a `PeerExchange`: `hrs` of `SmStg.upd_eq_step_v`. -/
theorem PeerExchange.rs_eq {d dp : D} {rv : Value} {y : ℝ} {bo bp : List (ℝ × ℝ)}
    (hx : PeerExchange d dp rv y) (hbo : bo.map Prod.fst = d.ownScores)
    (hbp : bp.map Prod.fst = dp.ownScores) :
    valFloat .f32 ((d.afterMax rv).afterSumR y).stg.rs =
      .ok (((bo ++ bp).map fun q => (2 : ℝ) ^ (slOf d.e * q.1 -
        (if Keep (alphaLog2 (slOf d.e) d.mE (max d.mE (blockMax (bo ++ bp)))) then d.mE.toReal
          else mSafe (max d.mE (blockMax (bo ++ bp)))) * slOf d.e)).sum) :=
  Sm.rs_eq hx.peer hx.own hx.partner hx.maxW hx.sumW (hx.rowOf hbo hbp) hbo hbp

end
end PTX.Kernels.InklingRelDecode.Proof.Sm

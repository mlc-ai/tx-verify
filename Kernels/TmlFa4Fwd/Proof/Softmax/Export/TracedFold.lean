-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RowHistory

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Numeric.OnlineFold
open PTX.Flow Softmax

noncomputable section

/-- Evaluate the numerical fold on the trace's sequence of round snapshots, including the
representation of a minus-infinite final maximum. -/
theorem traced_fold {p L m X g t S v} (hp : Pre p L m) (hn : 0 < t.n)
    (hist : RoundHistory p L X g t S t.n v)
    (rs : (softRow p L X g).rs = v.rs)
    (rm : (softRow p L X g).rm = (if v.mf then v.mr else 0)) :
    Fold t.n (weightOf p t (t.rowOf (Prologue.warpIndex L g/4) (rowIx L g)) S)
      (softRow p L X g).P (softRow p L X g).c (softRow p L X g).f (softRow p L X g).rs ∧
      (softRow p L X g).c (t.n-1) =
        (2:ℝ) ^ (-(abiFloat p.scaleLog2Bits * (softRow p L X g).rm)) := by
  let V' u := (roundSnapshot p L X g u).2
  let R u := (roundSnapshot p L X g u).1
  let M u := Data.maximum p L g (V' u) (R u)
  let W u k := Data.weight p (Data.score p L g (V' u) (R u) k)
  let row := t.rowOf (Prologue.warpIndex L g/4) (rowIx L g)
  have fold := Data.fold_states hp g t.n hn V' R ((hist.agree 0 hn).first.mp rfl)
    (fun u hu h => Nat.succ_ne_zero u ((hist.agree _ hu).first.mpr h)) hist.carry
  have last := hist.last (t.n-1) (by omega)
  have endLt : t.n-1 < t.n := by omega
  have weight (u) (hu : u<t.n) (k) (hk : k<128) :
      W u k = weightOf p t row S u k := (hist.agree u hu).weight k hk
  have sum : (∑ u ∈ Finset.range t.n, ∑ k ∈ Finset.range 128, W u k) =
      ∑ u ∈ Finset.range t.n, ∑ k ∈ Finset.range 128, weightOf p t row S u k :=
    Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun k hk =>
      weight u (Finset.mem_range.mp hu) k (Finset.mem_range.mp hk)
  have maxeq : (softRow p L X g).rm = (M (t.n-1)).toReal := by
    rw [rm,last.1,last.2.1]
    by_cases h : M (t.n-1) = ⊥
    · change (if finE (M _) then (M _).toReal else 0) = _
      simp only [h,finE,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,
        EReal.toReal_bot]
    · exact ite_eq_left (show finE (M (t.n-1)) = true from decide_eq_true h)
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_⟩
  · intro u hu
    rw [(hist.agree u hu).scale]
    exact fold.pos u hu
  · intro u hu k hk
    rw [(hist.agree u hu).pack k hk,(hist.agree u hu).scale,← weight u hu k hk]
    exact fold.prob u hu k hk
  · intro u hu
    rcases fold.factor u hu with ratio | masked
    · left
      rw [(hist.agree _ hu).factor,(hist.agree _ hu).scale,(hist.agree u (by omega)).scale]
      exact ratio
    · right
      intro a ha k hk
      exact (weight a (by omega) k hk).symm.trans (masked a ha k hk)
  · intro u hu; rw [(hist.agree u hu).factor]; exact fold.le u hu
  · rw [rs,last.2.2,(hist.agree _ endLt).scale]
    exact fold.sum.trans (congrArg (_ * ·) sum)
  · rw [(hist.agree _ endLt).scale,maxeq]
    simp only [Data.scale,scl,abiFloat,M,R,V',neg_mul]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values

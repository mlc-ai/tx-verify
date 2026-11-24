-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # A pair TMA ring slot's accesses are ordered

A proof tool over `Hyp`. Number a copy on the full barrier by its use (its producer's earlier
issues there over `n`) and a consumer's read by its use (the consumer's commits to the slot
before it, one fewer than its successful full polls). A copy and a read of one byte are ordered
one way or the other (`copy_read_order`): the copy precedes the read when its use is at most the
read's, and follows it otherwise, the producer's budget placing the copy's use below its
successful empty polls. Two copies of one byte by one producer in distinct uses are ordered
through a read of the byte in the earlier copy's use (`copies_chain`): the producer's poll for the
later use found every consumer's notification of the earlier one, so the reading consumer made the
commit of that use, and the kernel supplies its read of the byte in that use (`hread`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A tensor-core MMA or copy issue is not a commit. -/
theorem commits_tcAsync_succ {g k : Nat} {m : Loc} (h : X.TcAsync (g, k)) :
    ((X.tr g).take (k + 1)).countP (commitsTo m) = ((X.tr g).take k).countP (commitsTo m) := by
  rcases h with ⟨d, sp, ac, mk, pc, he⟩ | ⟨c, pc, he⟩ | ⟨s, pc, he⟩ <;>
  · rw [List.take_add_one, show (X.tr g)[k]? = _ from he]
    simp [commitsTo]

theorem tcAsync_lt {g k : Nat} (h : X.TcAsync (g, k)) : k < (X.tr g).length := by
  rcases h with ⟨d, sp, ac, mk, pc, he⟩ | ⟨c, pc, he⟩ | ⟨s, pc, he⟩ <;> exact len_of_get he

variable {nc : Nat} {S : Slot nc}

/-- **A copy and a read of one byte are ordered.** A copy on the full barrier and a read of
consumer `b` in a use (with fewer commits to the slot before it than successful full polls), at a
byte both cover, are ordered one way or the other. -/
theorem copy_read_order (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc}
    {km : Nat} (hR : X.TcAsync (S.cons b, km))
    (hcR : ((X.tr (S.cons b)).take km).countP (commitsTo (S.empty 0)) + 1 ≤
      okPolls S.full ((X.tr (S.cons b)).take km))
    {gl kl pcl al : Nat} {spl : TensorCopy.Spec}
    (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩) (hml : spl.mbar = S.full)
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (S.cons b, km) (.mmaRead isB idx) l) :
    AsyncBefore L X l ((gl, kl), .write (.load x y z)) ((S.cons b, km), .mmaRead isB idx) ∨
      AsyncBefore L X l ((S.cons b, km), .mmaRead isB idx) ((gl, kl), .write (.load x y z)) := by
  by_cases hle : ((X.tr gl).take kl).countP (issuesTo S.full) / S.n ≤
      ((X.tr (S.cons b)).take km).countP (commitsTo (S.empty 0))
  · exact .inl (copy_before_read hX H (tcAsync_lt hR) hel hml (by omega) hca hcb)
  · obtain ⟨a, rfl, hbud⟩ := issue_producer H hel hml
    have hq : ((X.tr (S.prod a)).take kl).countP (issuesTo S.full) / S.n <
        okPolls (S.empty a) ((X.tr (S.prod a)).take kl) :=
      (Nat.div_lt_iff_lt_mul H.n_pos).mpr (by rw [Nat.mul_comm]; omega)
    exact .inr (read_before_copy hX H hR hel (by rw [commits_tcAsync_succ hR]; omega) hcb hca).1

/-- **Two copies of one byte are ordered.** Copies of producer `a` at a byte both cover, the first
on the full barrier in the use of its producer's last successful empty poll before it and the
second after more such polls, are ordered through a read of consumer `b`: given `b`'s commit of
the first copy's use, `hread` names a read of `b` in that use covering the byte, present once a
wait observes its completion. -/
theorem copies_chain (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    {k1 k2 pc1 pc2 al1 al2 : Nat} {sp1 sp2 : TensorCopy.Spec}
    (he1 : X.get (S.prod a, k1) = some ⟨pc1, .tensorIssue al1 sp1⟩) (hm1 : sp1.mbar = S.full)
    (he2 : X.get (S.prod a, k2) = some ⟨pc2, .tensorIssue al2 sp2⟩)
    (hlt : okPolls (S.empty a) ((X.tr (S.prod a)).take k1) <
      okPolls (S.empty a) ((X.tr (S.prod a)).take k2))
    (huse : ((X.tr (S.prod a)).take k1).countP (issuesTo S.full) / S.n + 1 =
      okPolls (S.empty a) ((X.tr (S.prod a)).take k1))
    {x y z x' y' z' : Nat} {l : Loc}
    (hca : AsyncCovers X (S.prod a, k1) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (S.prod a, k2) (.write (.load x' y' z')) l) (b : Fin nc)
    (hread : ∀ jc pc sp, X.get (S.cons b, jc) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = S.empty 0 →
      ((X.tr (S.cons b)).take jc).countP (commitsTo (S.empty 0)) =
        ((X.tr (S.prod a)).take k1).countP (issuesTo S.full) / S.n →
      ∃ kR isB idx, X.TcAsync (S.cons b, kR) ∧
        ((X.tr (S.cons b)).take kR).countP (commitsTo (S.empty 0)) =
          ((X.tr (S.prod a)).take k1).countP (issuesTo S.full) / S.n ∧
        ((X.tr (S.cons b)).take kR).countP (commitsTo (S.empty 0)) + 1 ≤
          okPolls S.full ((X.tr (S.cons b)).take kR) ∧
        AsyncCovers X (S.cons b, kR) (.mmaRead isB idx) l ∧
        ∀ w ws, AsyncObserved X (S.cons b, kR) .mmaDone w true ws →
          X.AsyncPresent (S.cons b, kR) (.mmaRead isB idx)) :
    AsyncChain L X l ((S.prod a, k1), .write (.load x y z))
      ((S.prod a, k2), .write (.load x' y' z')) := by
  generalize hu : ((X.tr (S.prod a)).take k1).countP (issuesTo S.full) / S.n = u at huse hread
  -- The producer's poll for use `Q` found every notification of `b` of the uses below `Q`.
  obtain ⟨jl, pcw, pw, acqw, scw, -, hwl, hcl⟩ := MbarRing.Poll.exists_nth (X := X)
    (g := S.prod a) (k := k2) (m := S.empty a)
    (n := okPolls (S.empty a) ((X.tr (S.prod a)).take k1)) (by omega)
  obtain ⟨jr, w, -, -, -, -, -, hnot⟩ := producer_poll hX H hwl
    (q := okPolls (S.empty a) ((X.tr (S.prod a)).take k1) - 1) (by omega)
  have hcom := notified_commits hX H (hnot b)
  -- `b`'s commit of use `Q - 1`.
  obtain ⟨jc, ec, hec, hecc, hcjc⟩ := MbarRing.Slot.exists_nth_countP
    (commitsTo (S.empty 0)) (xs := X.tr (S.cons b))
    (c := u) (by omega)
  obtain ⟨pcc, spc, rfl, hmc⟩ : ∃ pcc spc, ec = ⟨pcc, .tc (.commit spc)⟩ ∧
      spc.mbar = S.empty 0 := by
    obtain ⟨pcc, kd⟩ := ec
    cases kd with
    | tc k =>
      cases k with
      | commit spc =>
        simp only [commitsTo, decide_eq_true_eq] at hecc
        exact ⟨pcc, spc, rfl, hecc⟩
      | _ => simp [commitsTo] at hecc
    | _ => simp [commitsTo] at hecc
  obtain ⟨kR, isB, idx, hR, hcr, hcR, hcbR, hpres⟩ := hread jc pcc spc hec hmc hcjc
  have hWR := copy_before_read hX H (tcAsync_lt hR) he1 hm1 (by rw [hu]; omega) hca hcbR
  obtain ⟨hRW, w', ws', hom⟩ := read_before_copy hX H hR he2
    (by rw [commits_tcAsync_succ hR]; omega) hcbR hcb
  exact .tail (.direct hWR) (hpres w' ws' hom) hRW

end
end PTX.PairTmaRing

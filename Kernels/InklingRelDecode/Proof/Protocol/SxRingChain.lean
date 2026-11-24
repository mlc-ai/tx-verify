-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.KvSingle

@[expose] public section

/-!
# Two copies of one KV slot byte, of two uses, are ordered

Port of `Lemmas/Protocol/PairTmaRing/Ordered.lean` (`copies_chain`) to `Kv.Slot`. A copy of the
slot's use `u` and a copy of a later use, both writing byte `l`, are ordered through an MMA read
of `l` in use `u` (`copies_chain`):

* the later copy is the loader's (the prologue's copies are of use 0), within its budget of eight
  per successful poll of `empty`, so the loader polled `empty` for use `u + 1`, and that poll
  observed the MMA lane's notification of its commit with `u` earlier ones (`producer_observes`,
  `SE_op`): the commit is an event of the execution;
* before that commit the MMA lane read `l` in use `u` (the premise `hcover`, a fact of the MMA
  warp's run: its reads of a use cover the slot);
* the first copy is before that read (`copy_before_read`), and the read before the second copy
  (`read_before_copy`), whose observation makes the read present.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Kv
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {S : Slot}

/-- A copy on the full barrier of a positive use is the loader's copy thread's. -/
theorem copy_cp_of_pos (H : Hyp L K A X S) {g k pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full)
    (hpos : 0 < copyUse X S (g, k)) :
    g = S.cp ∧ ((X.tr g).take k).countP (issuesTo S.full) + 1 ≤
      8 * okPolls S.empty ((X.tr g).take k) := by
  rcases H.issue he hm with h | ⟨hδ1, i, hi⟩
  · exact h
  · exfalso
    have : copyUse X S (g, k) = 0 := by simp [copyUse, hδ1, hi]
    omega

/-- **The MMA lane's commit of use `u` exists** once a copy of a later use was issued. -/
theorem commit_of_later_copy (hX : Consistent L K A mem0 X) (H : Hyp L K A X S)
    {g k pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full) {u : Nat}
    (hu : u < copyUse X S (g, k)) :
    ∃ jc pcc spc, X.get (S.cm, jc) = some ⟨pcc, .tc (.commit spc)⟩ ∧ spc.mbar = S.empty ∧
      ((X.tr S.cm).take jc).countP (commitsTo S.empty) = u := by
  obtain ⟨rfl, hb⟩ := copy_cp_of_pos H he hm (by omega)
  have hδ := H.δ_le
  have hnp : ¬ (S.δ = 1 ∧ ∃ i : Fin 8, (S.cp, k) = S.pCp i) := by
    rintro ⟨hδ1, i, hi⟩
    exact (H.pre_ne hδ1).2 i (congrArg Prod.fst hi).symm
  have hcu : copyUse X S (S.cp, k) =
      ((X.tr S.cp).take k).countP (issuesTo S.full) / 8 + S.δ := by
    simp [copyUse, hnp]
  have hle := okPolls_take_le S.empty (X.tr S.cp) k
  have hj : u + 1 - S.δ < okPolls S.empty (X.tr (S.prod 1)) := by
    rw [prod_one]
    omega
  obtain ⟨hy, -, -⟩ := producer_observes hX H (a := 1) (n := u) hj 0
  obtain ⟨-, ⟨pcc, spc, hcm, hmb, -, hcnt⟩, -⟩ := SE_op H hy
  exact ⟨(cmE X S 0 u).2, pcc, spc, hcm, hmb, hcnt⟩

/-- **Two copies of one byte in two uses are ordered**, through a read of the byte in the first
copy's use that the MMA lane makes before its commit of that use (`hcover`). -/
theorem copies_chain (hX : Consistent L K A mem0 X) (H : Hyp L K A X S)
    {g1 k1 pc1 al1 g2 k2 pc2 al2 : Nat} {sp1 sp2 : TensorCopy.Spec}
    (he1 : X.get (g1, k1) = some ⟨pc1, .tensorIssue al1 sp1⟩) (hm1 : sp1.mbar = S.full)
    (he2 : X.get (g2, k2) = some ⟨pc2, .tensorIssue al2 sp2⟩) (hm2 : sp2.mbar = S.full)
    (hlt : copyUse X S (g1, k1) < copyUse X S (g2, k2))
    {x y z x' y' z' : Nat} {l : Loc}
    (hca : AsyncCovers X (g1, k1) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (g2, k2) (.write (.load x' y' z')) l)
    (hcover : ∀ jc pc sp, X.get (S.cm, jc) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = S.empty →
      ((X.tr S.cm).take jc).countP (commitsTo S.empty) = copyUse X S (g1, k1) →
      ∃ kR isB idx, X.TcAsync (S.cm, kR) ∧
        readUse X S (S.cm, kR) = copyUse X S (g1, k1) ∧
        copyUse X S (g1, k1) + 1 ≤ okPolls S.full ((X.tr S.cm).take kR) ∧
        AsyncCovers X (S.cm, kR) (.mmaRead isB idx) l ∧
        ∀ w ws, AsyncObserved X (S.cm, kR) .mmaDone w true ws →
          X.AsyncPresent (S.cm, kR) (.mmaRead isB idx)) :
    AsyncChain L X l ((g1, k1), .write (.load x y z)) ((g2, k2), .write (.load x' y' z')) := by
  obtain ⟨jc, pcc, spc, hcm, hmb, hcnt⟩ := commit_of_later_copy hX H he2 hm2 hlt
  obtain ⟨kR, isB, idx, hR, hru, hpol, hcR, hpres⟩ := hcover jc pcc spc hcm hmb hcnt
  have hWR := copy_before_read hX H (tcAsync_lt hR) he1 hm1 hpol hca hcR
  obtain ⟨rfl, -⟩ := copy_cp_of_pos H he2 hm2 (by omega)
  obtain ⟨hRW, w, ws, hom⟩ := read_before_copy hX H hR he2 hm2
    (by rw [commits_tcAsync_succ hR]; unfold readUse at hru; simp only at hru; omega) hcR hcb
  exact .tail (.direct hWR) (hpres w ws hom) hRW

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Kv

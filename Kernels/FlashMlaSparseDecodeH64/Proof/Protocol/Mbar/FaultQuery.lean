-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.FaultTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Obj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Count
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
public import Lemmas.Protocol.GatedFaults

@[expose] public section

/-! # The query and closing barriers do not fault

Three barriers are used once per lane: `lastStoreDone` (one arrival per warpgroup-0 lane, so no
arrival has an earlier one: `wg0_lastArr`), `qUtccp` (one commit of the MMA lane, `mma_commits_le`)
and `qTma` (one arrival and eight tensor loads of the MMA lane, `mma_arrivals_le`,
`mma_issues_le`). An update of a use `t ≥ 1` is then none, so every gate is vacuous. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **No record of `lastStoreDone` faults.** -/
theorem lastStore_fault (c : Nat) :
    ∀ r ∈ X.objects (mbarLoc L c .lastStoreDone), r.fault = none := by
  refine (lastStore_obj hp hX hFw hR hI hB c).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have h0 : arrivals (mbarLoc L c .lastStoreDone) ((X.tr (wg0Lane L c a)).take i) = 0 :=
    wg0_lastArr hp hX hFw (c := c) (b := a.val) a.isLt he
  omega

/-- **No record of `qUtccp` faults.** -/
theorem qUtccp_fault (c : Nat) :
    ∀ r ∈ X.objects (mbarLoc L c .qUtccp), r.fault = none := by
  refine (qUtccp_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) (c := c)).fault_free hX
    (Notify.gated_of_paths (K := kernel) (A := Assumptions.all) fun {i pc sp rank}
      hget hb ht hrec hpos => ?_)
  exfalso
  have hw4 := mma_commit_warp hp hX hFw hget
  have hc : mmaLane L X c / L.block = c := by
    rcases qUtccp_use hR (Frame.lt_of_get hX hget) hget ⟨rank, ht⟩ with ⟨n, hk⟩ | ⟨hc, -⟩
    · cases hk
    · exact hc
  have hC1 : ((X.tr (mmaLane L X c)).countP (PTX.Flow.commitsTo (mbarLoc L c .qUtccp))) ≤ 1 := by
    have := mma_commits_le hp hX hFw hw4
    rw [flow_commitsTo] at this
    simpa only [MbarRow.loc, hc, flow_commitsTo] using this
  have hlt := countP_lt_of_get (p := PTX.Flow.commitsTo (mbarLoc L c .qUtccp)) hget
    (by simp [PTX.Flow.commitsTo, hb])
  dsimp only at hlt
  omega

/-- **No record of `qTma` faults**: the MMA lane arrives once and loads eight times, so no item
has a use `t ≥ 1`. -/
theorem qTma_fault (c : Nat) :
    ∀ r ∈ X.objects (mbarLoc L c .qTma), r.fault = none := by
  have O := qTma_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) (c := c)
  -- the lane's counts are bounded as soon as it has an event on the barrier
  have hbd : ∀ {j pc : Nat} {kd : Kind}, X.get (mmaLane L X c, j) = some ⟨pc, kd⟩ →
      Frame.MbarOf ⟨pc, kd⟩ (mbarLoc L c .qTma) → (∀ n, kd ≠ .mbInit (mbarLoc L c .qTma) n) →
      (∀ q ok acq sc, kd ≠ .wait (mbarLoc L c .qTma) q ok acq sc) →
      (X.tr (mmaLane L X c)).countP (issuesTo (mbarLoc L c .qTma)) ≤ 8 ∧
        arrivals (mbarLoc L c .qTma) (X.tr (mmaLane L X c)) ≤ 1 := by
    intro j pc kd he hm hni hnw
    rcases qTma_use hR (Frame.lt_of_get hX he) he hm with ⟨n, hk⟩ | ⟨hon, hc, -⟩
    · exact absurd hk (hni n)
    have hw4 : MbarRow.warp L (mmaLane L X c) = 4 := hon.1.1
    refine ⟨?_, ?_⟩
    · have := mma_issues_le hp hX hFw hw4
      simpa only [MbarRow.loc, hc] using this
    · have := mma_arrivals_le hp hX hFw hw4 (mbarLoc L c .qTma)
      exact this
  refine O.fault_free hX (by decide) (by decide) ?_ ?_
  · intro k r x hk hid hact hpos
    rcases id hact with ⟨c', tx, ha⟩ | ⟨b, ha⟩
    · obtain ⟨j, pc, rel, sc, he, hc, -⟩ := tma_arrive_item O hk hid ha
      obtain ⟨-, hA⟩ := hbd he rfl (fun n h => by cases h) (fun q ok acq sc h => by cases h)
      have hlt := countP_lt_of_get (p := arrivesOn (mbarLoc L c .qTma)) he
        (by simp [arrivesOn, sourceArrive])
      simp only [arrivals] at hc hA
      dsimp only at hlt
      omega
    · obtain ⟨j, pc, al, sp, he, hm, hc, -⟩ := tma_copy_item O hk hid ha
      obtain ⟨hN, -⟩ := hbd he hm (fun n h => by cases h) (fun q ok acq sc h => by cases h)
      have hlt := countP_lt_of_get (p := issuesTo (mbarLoc L c .qTma)) he
        (by rw [issuesTo_tensorIssue]; simpa using hm)
      dsimp only at hlt
      omega
  · intro t hnot x hx
    obtain ⟨-, h0, h1⟩ := O.source hx
    have hb : (X.tr (mmaLane L X c)).countP (issuesTo (mbarLoc L c .qTma)) ≤ 8 ∧
        arrivals (mbarLoc L c .qTma) (X.tr (mmaLane L X c)) ≤ 1 := by
      by_cases hz : x.1.val = 0
      · obtain ⟨⟨pc, rel, sc, hget⟩, -⟩ := h0 hz
        exact hbd hget rfl (fun n h => by cases h) (fun q ok acq sc h => by cases h)
      · obtain ⟨⟨pc, al, sp, hget, hm⟩, -⟩ := h1 hz
        exact hbd hget hm (fun n h => by cases h) (fun q ok acq sc h => by cases h)
    rw [qTma_items O hb.1 hb.2 hx]
    exact Nat.zero_le _

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

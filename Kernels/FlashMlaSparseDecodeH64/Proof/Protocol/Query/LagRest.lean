-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.LagMma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count

@[expose] public section

/-! # The `qUtccp` waits of the TMA and dequant lanes (pcs 2205, 2644)

A waiter's poll has parity 0 and no successful poll before it (`qUtccp_first`). The object is
the MMA lane's notify object (`qUtccp_obj`) with its final state (the waiter is past barrier 0:
`bar0_next`, `objects_ne`). At an even phase the notify blocker (`Notify.Obj.blocker`, reuse
paths `qUtccp_reach` with at most one commit, `mma_commits_le`) gives either an undelivered
commit notification (an open `.commit` obligation, as for the MMA lane's own wait,
`qUtccp_mmaBlk`) or no commit of the CTA's MMA lane. In that case the CTA's MMA producer
(`MmaProd`, `mma_producer`) has not committed either (a lane that committed to `qUtccp` is the
CTA's `mmaLane`, `qut_lane`), and the schedule `qUtccp_lagE` (`τ = qUtccpSlot`, `δ = 0`,
`U = 1`; the producer before the election: `electSlot < qUtccpSlot`; after it:
`mma_qUtEarly`, `mma_qUtExit`) makes it a blocker. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The producer of `qUtccp` of CTA `c` while it lags: the CTA's MMA producer before its
commit. -/
def QProdE (P : Params) (L : Launch) (X : Execution) (c y : Nat) : Prop :=
  MmaProd P L X c y ∧ (X.tr y).countP (commitsTo (mbarLoc L c .qUtccp)) = 0

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The `qUtccp` schedule from the election on.** -/
theorem qUtccp_lagE (hR : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows P L Y)
    (hnu : ¬ HasUb X) (hT : QueryTime P L m X) (c : Nat) :
    Sched.LagN (timed P L) X (mbarLoc L c .qUtccp) 0 (QProdE P L X c) (QWaitNext L m X c)
      (fun _ => qUtccpSlot) 1 (commitsTo (mbarLoc L c .qUtccp)) := by
  have H := qUtccp_lag hp hX hFw hR hnu hT c
  refine ⟨H.mono, H.wait, fun y hy _ => ?_, fun y k pc hy hx => ?_, H.bound⟩
  · obtain ⟨⟨hyc, -, ⟨-, ht⟩ | ⟨k, e0, he0, hu0, hon⟩⟩, h0⟩ := hy
    · have := elect_lt_q
      omega
    · exact mma_qUtEarly hp hX hFw hnu he0 hu0 hon (by simp only [MbarRow.loc, hyc]; exact h0)
  · obtain ⟨⟨hyc, -, ⟨hnx, -⟩ | ⟨k0, e0, he0, hu0, hon⟩⟩, -⟩ := hy
    · exact (hnx k pc hx).elim
    · have := mma_qUtExit hp hX hFw he0 hu0 hon hx
      simp only [MbarRow.loc, hyc] at this
      exact this

/-- **A lane that committed to `qUtccp` of CTA `c` is the CTA's MMA lane**, of warp 4. -/
theorem qut_lane (hR : MbarRows P L X) {z c : Nat}
    (hpos : 0 < (X.tr z).countP (commitsTo (mbarLoc L c .qUtccp))) :
    z = mmaLane L X c ∧ MbarRow.warp L z = 4 ∧ z / L.block = c := by
  obtain ⟨e, hmem, hpe⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  have he : X.get (z, k) = some e := hk
  obtain ⟨sp, hks, hsm⟩ := Notify.commit_of_commitsTo hpe
  obtain ⟨pce, kd⟩ := e
  simp only at hks
  subst hks
  obtain ⟨rank, ht⟩ := mma_commitHit hp hX he hsm
  have hm : Frame.MbarOf ⟨pce, .tc (.commit sp)⟩ (mbarLoc L c .qUtccp) := ⟨rank, ht⟩
  rcases qUtccp_use hR (Frame.lt_of_get hX he) he hm with ⟨n, hk'⟩ |
    ⟨hzc, ⟨hat, -, -⟩ | ⟨-, ⟨ok', hk'⟩, -⟩⟩
  · cases hk'
  · refine ⟨?_, hat.1.1, hzc⟩
    rw [← hzc]
    exact laneOn_eq (mmaOne hp hX hFw) he (fun _ h => by cases h) hat
  · cases hk'

/-- **A waiter of `qUtccp` at pc 2205 or 2644 is blocked**, when the object's records do not
fault: by the MMA commit's undelivered notification, or by the MMA producer before its
commit. -/
theorem qUtccp_restBlk (hR : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows P L Y)
    (hI : InitRows L X) (hB : Bar0Rows L X) (hT : QueryTime P L m X) (hub : ¬ HasUb X)
    {g pc : Nat} {sc : MbarScope} (hw : QWaiter L g pc)
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g .qUtccp), r.fault = none)
    (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait (MbarRow.loc L g .qUtccp) 0 false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g .qUtccp) 0 := by
  simp only [MbarRow.loc] at hff hn ⊢
  have hg := hn.lt
  have hRx := hR X hX
  have hgN : QWaitNext L m X (g / L.block) g := ⟨hg, rfl, pc, 0, false, true, sc, hw, hn⟩
  have h0g := qUtccp_first hR hgN
  have hpc97 : 97 < pc := by rcases hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hb0 := bar0_next hp hFw hn (fun _ h => by cases h) hpc97
  have N := qUtccp_obj hp hX hFw hRx hI hB (mmaOne hp hX hFw) (c := g / L.block)
  obtain ⟨st, hst⟩ := Unit.final_of_init hX N.init N.noInval
    (objects_ne hp hX hFw hI hg (.inr ⟨rfl, hrel⟩) (k := (X.tr g).length)
      (by rwa [List.take_length]) .qUtccp)
  refine ⟨st, hst, fun hpar => ?_⟩
  have hC1 : (X.tr (mmaLane L X (g / L.block))).countP
      (commitsTo (mbarLoc L (g / L.block) .qUtccp)) ≤ 1 := by
    by_contra hlt
    obtain ⟨-, hw4, hzc⟩ := qut_lane hp hX hFw hRx (z := mmaLane L X (g / L.block))
      (c := g / L.block) (by omega)
    have := mma_commits_le hp hX hFw hw4
    simp only [MbarRow.loc, hzc] at this
    omega
  obtain ⟨hle, hb'⟩ := N.blocker hX (qUtccp_reach N hC1 g) hff
    (fun he' hm' => mma_commitHit hp hX he' hm') hst (by rw [h0g]; simpa using hpar)
    (Nat.zero_le _)
  rcases hb' with hb' | hb'
  · have hne : X.tr g ≠ [] := by
      intro h
      simp [h] at hb0
    obtain ⟨y, hyt, hyP, -⟩ := mma_producer hp hX hFw hub (c := g / L.block) (by
      have := hp.block
      have := Nat.div_mul_le_self g L.block
      omega)
    have h0y : (X.tr y).countP (commitsTo (mbarLoc L (g / L.block) .qUtccp)) = 0 := by
      by_contra hpos
      obtain ⟨hym, -⟩ := qut_lane hp hX hFw hRx (z := y) (c := g / L.block)
        (by omega)
      rw [hym] at hpos
      omega
    exact (qUtccp_lagE hp hX hFw hR hub hT (g / L.block)).blk hX hub hg hgN hne ⟨hyP, h0y⟩ hyt
      (by rw [hyP.1]) (by rw [h0y, h0g])
  · exact .inl ⟨.commit, by simp, hb'⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

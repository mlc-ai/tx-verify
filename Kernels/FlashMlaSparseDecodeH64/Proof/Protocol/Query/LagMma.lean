-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Lag
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Commit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
public import Lemmas.Protocol.NotifyBlocker
public import Lemmas.Protocol.UnitReachBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.StartInit
import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

/-! # The MMA lane's own `qUtccp` wait row (pc 1983)

The MMA lane waits on `qUtccp` right after its own commit to it (pc 1982), so it is its own
producer and no time fact is needed. At the wait it has no successful poll and one commit
(`mma_qUt_wait`); it is the CTA's MMA lane (its commit is a use of the object, `qUtccp_use`,
`mmaOne`), so the object is its notify object (`qUtccp_obj`). The object has its initialization
record (the commit follows the lane's barrier-0 event, so the CTA's elected startup lane
initialized it: `use_after_bar0`, `won_inits`), hence a final state. When that state's phase is
even, `Notify.Obj.blocker` (reuse paths vacuous with one commit, `qUtccp_reach`; each commit
targets its mbarrier, `mma_commitHit`) bounds the phase by the lane's successful polls, 0, so the
one commit is not a counted unit: its notification is undelivered, an open `.commit` obligation. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The MMA lane at its wait on `qUtccp` is blocked** by its commit's undelivered
notification, when the object's records do not fault. -/
theorem qUtccp_mmaBlk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    {g pc : Nat} {ok acq : Bool} {sc : MbarScope}
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g .qUtccp), r.fault = none)
    (hw : MbarRow.warp L g = 4) (hr : 1850 ≤ pc ∧ pc < 2162)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait (MbarRow.loc L g .qUtccp) 0 ok acq sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g .qUtccp) 0 := by
  obtain ⟨h0, h1⟩ := mma_qUt_wait hp hX hFw hw hn hr
  simp only [MbarRow.loc] at h0 h1 hff
  -- the lane's commit, a use of the object
  obtain ⟨e, hmem, hpe⟩ := List.countP_pos_iff.mp (show 0 < (X.tr g).countP
    (commitsTo (mbarLoc L (g / L.block) .qUtccp)) by omega)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  have he : X.get (g, k) = some e := hk
  obtain ⟨sp, hks, hsm⟩ := Notify.commit_of_commitsTo hpe
  obtain ⟨pce, kd⟩ := e
  simp only at hks
  subst hks
  obtain ⟨rank, ht⟩ := mma_commitHit hp hX he hsm
  have hg := Frame.lt_of_get hX he
  have hm : Frame.MbarOf ⟨pce, .tc (.commit sp)⟩ (mbarLoc L (g / L.block) .qUtccp) := ⟨rank, ht⟩
  -- the lane is the CTA's MMA lane
  have hy : g = mmaLane L X (g / L.block) := by
    rcases qUtccp_use hR hg he hm with ⟨n, hk'⟩ | ⟨-, ⟨hat, -, -⟩ | ⟨-, ⟨ok', hk'⟩, -⟩⟩
    · cases hk'
    · exact laneOn_eq (mmaOne hp hX hFw) he (fun _ h => by cases h) hat
    · cases hk'
  have N := qUtccp_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) (c := g / L.block)
  rw [← hy] at N
  -- the object has its initialization record, hence a final state
  have hpos := use_after_bar0 hp hX hFw he hm (fun c' h => by cases h)
  obtain ⟨g0, j, kb, mk, inst, pcb, cnt, mode, hcg, hj, hb, h0j, h0b⟩ :=
    hI.winner hg (.inl (List.getElem?_eq_some_iff.mp he).1) hpos
  obtain ⟨i, -, pci, hgi⟩ := won_inits hp hX hFw hj rfl hb h0j h0b .qUtccp
  rw [hcg] at hgi
  obtain ⟨_, r, hr0, -⟩ := init_record_of_actual_get hX hgi
  have hne : X.objects (mbarLoc L (g / L.block) .qUtccp) ≠ [] := by
    intro hnil
    rw [hnil] at hr0
    simp at hr0
  obtain ⟨st, hst⟩ := Unit.final_of_init hX N.init N.noInval hne
  refine ⟨st, hst, fun hpar => ?_⟩
  obtain ⟨hle, hb'⟩ := N.blocker hX (qUtccp_reach N (by omega) g) hff
    (fun he' hm' => mma_commitHit hp hX he' hm') hst (by rw [h0]; simpa using hpar)
    (Nat.zero_le _)
  rcases hb' with hb' | hb'
  · omega
  · exact .inl ⟨.commit, by simp, hb'⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

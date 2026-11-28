-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.LagQk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Obj
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Wait
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Wait
import Lemmas.Protocol.KindRingBlock

@[expose] public section

/-! # The PV channel's progress rows (`sv_done`, waits at 2684 and 1184)

`svDone j` of CTA `c` is a commit object of the CTA's MMA lane (`svDone_obj`): block `r` of slot
`j = r % 2` is completed by its commit at `svCommit r`.

* **The dequant lanes** (pc 2684, offset 1) wait for the use `u` (their successful polls) at
  `svWaitD (2u + j)`, after the commit of block `2(u-1) + j` (`sv_lt_d`). The schedule
  (`svDone_lag`, `δ = 1`): `τ u = svCommit (2(u-1)+j) + 1` (`0` for the first use), producers the
  CTA's MMA producer short of the CTA's uses of the slot (`mma_svEarly`, `mma_svExit`, before the
  election `elect_lt`). At a blocked poll (`svDone_dqBlk`) the final phase is one below the lane's
  polls (`KRing.E_phase_le`, `KRing.E_phase` on the dequantized buffer ring `dqSlot`: also the
  first use), and every commit delivered makes the phase at least the MMA lane's commits
  (`Notify.Obj.phase_ge_of_records`), so the MMA producer is short of the waited use.
* **Warpgroup 0** (pc 1184) waits once, after its last block `R - 1` (`R = blocksOf`, at least
  one: `blocksOf_pos`), on its slot with that block's parity, at `svWaitW0 R` (`wg0_svWait`). At
  a blocked poll (`svDone_w0Blk`) the MMA producer either is short of the slot's uses `U` (then it
  is earlier than `svCommit (R - 1) < svWaitW0 R`, `sv_lt_w0`, and does not exit: it lags), or it
  made all `U` of them: then with every commit delivered the phase is the MMA lane's commits
  (`phase_le_commit_count`, `phase_ge_of_records`), which are `U` (`mma_svCommits_le`), whose
  parity is not the waited one. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The producer of `svDone j` of CTA `c` while it lags: the CTA's MMA producer short of the uses
of the slot. -/
def SvProd (P : Params) (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) (y : Nat) : Prop :=
  MmaProd P L X c y ∧
    (X.tr y).countP (commitsTo (mbarLoc L c (.svDone j))) < ringUses 2 j.val (blocksOf P L c)

/-- Lane `g`'s next event is a dequant lane's wait at 2684 on `svDone j` of CTA `c`. -/
def SvCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (j : Fin 2) (g : Nat) : Prop :=
  ∃ p ok acq sc, Sched.NextEv L kernel Assumptions.all m X g
    ⟨2684, .wait (mbarLoc L c (.svDone j)) p ok acq sc⟩

private theorem svCommit_mono {a b : Nat} (h : a ≤ b) : svCommit a ≤ svCommit b := by
  simp only [svCommit, frame, stride, loopBase, mmaOff, mmaPvc]
  omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The `svDone` schedule of the dequant lanes** for slot `j` of CTA `c`. -/
theorem svDone_lag (hub : ¬ HasUb X) (c : Nat) (j : Fin 2) :
    Sched.LagN (timed P L) X (mbarLoc L c (.svDone j)) 1 (SvProd P L X c j) (SvCons L m X c j)
      (fun u => if u = 0 then 0 else svCommit (2 * (u - 1) + j.val) + 1)
      (ringUses 2 j.val (blocksOf P L c)) (commitsTo (mbarLoc L c (.svDone j))) := by
  refine ⟨fun a b h => ?_, fun g hg => ?_, fun y hy _ => ?_, fun y k pc hy hx => ?_,
    fun g hg => ?_⟩
  · have := svCommit_mono (a := 2 * (a - 1) + j.val) (b := 2 * (b - 1) + j.val) (by omega)
    split_ifs <;> omega
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    obtain ⟨-, -, hw⟩ := deq_svWait hp hX hFw hn
    split_ifs with h0
    · exact Nat.zero_le _
    · have := sv_lt_d (2 * (okPolls (mbarLoc L c (.svDone j)) (X.tr g) - 1) + j.val)
      rw [show 2 * (okPolls (mbarLoc L c (.svDone j)) (X.tr g) - 1) + j.val + 2 =
        2 * okPolls (mbarLoc L c (.svDone j)) (X.tr g) + j.val by omega] at this
      omega
  · obtain ⟨⟨hyc, -, ⟨-, ht⟩ | ⟨k, e0, he0, hu0, hon⟩⟩, hlt⟩ := hy
    · have := elect_lt (2 * (X.tr y).countP (commitsTo (mbarLoc L c (.svDone j))) + j.val)
        (mmaOff + mmaPvc)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, svCommit]
      omega
    · have := mma_svEarly hp hX hFw hub he0 hu0 hon hyc hlt
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      omega
  · obtain ⟨⟨hyc, -, ⟨hnx, -⟩ | ⟨k0, e0, he0, hu0, hon⟩⟩, -⟩ := hy
    · exact (hnx k pc hx).elim
    · exact mma_svExit hp hX hFw he0 hu0 hon hyc hx
  · obtain ⟨p, ok, acq, sc, hn⟩ := hg
    have := (deq_svWait hp hX hFw hn).2.1
    omega

variable (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hR hI hB

omit hI hB in
/-- The MMA producer of the waiter's CTA made no more commits to `svDone s` than the CTA's MMA
lane. -/
private theorem prod_le (hub : ¬ HasUb X) {g : Nat} (hg : g < L.threads) (s : Fin 2) :
    ∃ y, y < L.threads ∧ MmaProd P L X (g / L.block) y ∧
      (X.tr y).countP (commitsTo (mbarLoc L (g / L.block) (.svDone s))) ≤
        (X.tr (mmaLane L X (g / L.block))).countP
          (commitsTo (mbarLoc L (g / L.block) (.svDone s))) := by
  obtain ⟨y, hyt, hyP, -⟩ := mma_producer hp hX hFw hub (c := g / L.block) (by
    have := hp.block
    have := Nat.div_mul_le_self g L.block
    omega)
  refine ⟨y, hyt, hyP, ?_⟩
  by_cases h0 : (X.tr y).countP (commitsTo (mbarLoc L (g / L.block) (.svDone s))) = 0
  · omega
  · obtain ⟨hym, -⟩ := score_lane hp hX hFw hR (z := y) (c := g / L.block) ⟨s, .inr rfl⟩
      (by omega)
    rw [hym]

/-- With every commit delivered, the phase of `svDone s` is at least the MMA lane's commits. -/
private theorem phase_ge (c : Nat) (s : Fin 2)
    (hff : ∀ r ∈ X.objects (mbarLoc L c (.svDone s)), r.fault = none)
    (hall : ∀ i sp rank m', X.Commit i sp → TcCommit.target sp rank = some m' →
      rank ∈ X.tcNotified i) {st : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (mbarLoc L c (.svDone s)))
      (X.objects (mbarLoc L c (.svDone s))).length = some st) :
    (X.tr (mmaLane L X c)).countP (commitsTo (mbarLoc L c (.svDone s))) ≤ st.phase :=
  (svDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s).phase_ge_of_records hX hst le_rfl
    fun _ ht => Notify.Obj.notified_rec hX hff (fun he' hm' => mma_commitHit hp hX he' hm') hall ht

/-- **A dequant lane's wait on `svDone s` is blocked**, when the object's records do not fault:
by an undelivered commit notification, or by the CTA's MMA producer short of the waited use. -/
theorem svDone_dqBlk (hN : DequantInputs L X) (hub : ¬ HasUb X) {g q : Nat} {s : Fin 2}
    {sc : MbarScope} (hb0 : 0 < (X.tr g).countP isBar0)
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.svDone s)), r.fault = none)
    (hq : q = (okPolls (MbarRow.loc L g (.svDone s)) (X.tr g) + 1) % 2)
    (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2684, .wait (MbarRow.loc L g (.svDone s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.svDone s)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  obtain ⟨⟨-, hw8, hw12⟩, hlt, -⟩ := deq_svWait hp hX hFw hn
  have hg := hn.lt
  obtain ⟨b, hb⟩ := deq_lane hp (pc := 2684) ⟨hw8, hw12, by decide, by decide⟩
  have N := svDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) (g / L.block) s
  have hb0' : 0 < ((X.tr g).take (X.tr g).length).countP isBar0 := by
    rw [List.take_length]
    exact hb0
  obtain ⟨st, hst⟩ := Unit.final_of_init hX N.init N.noInval
    (objects_ne hp hX hFw hI hg (.inr ⟨rfl, hrel⟩) hb0' (.svDone s))
  refine ⟨st, hst, fun hpar => ?_⟩
  rw [hq, Nat.mod_mod] at hpar
  have hle := (dqSlot hp hX hFw hR hI hB hN (g / L.block) s).E_phase_le hX one_pos N.init
    (fun r hr hi => by
      cases N.src r hr with
      | init ha | poll _ _ ha | commit _ _ _ _ ha => rw [hi] at ha; cases ha)
    (fun hk _ ha => (N.arrive_rec hk ha).1)
    (fun hk hf ha => N.rec_S hk hf ha) b hst
  have hph := (dqSlot hp hX hFw hR hI hB hN (g / L.block) s).E_phase hX b hst hle (by
    change st.phase % 2 = (okPolls (mbarLoc L (g / L.block) (.svDone s))
      (X.tr (deqLane L (g / L.block) b)) + 1) % 2
    rw [← hb]
    exact hpar)
  change st.phase + 1 = okPolls (mbarLoc L (g / L.block) (.svDone s))
    (X.tr (deqLane L (g / L.block) b)) at hph
  rw [← hb] at hph
  by_cases hall : ∀ i sp rank m', X.Commit i sp → TcCommit.target sp rank = some m' →
      rank ∈ X.tcNotified i
  · have hge := phase_ge hp hX hFw hR hI hB (g / L.block) s hff hall hst
    obtain ⟨y, hyt, hyP, hCy⟩ := prod_le hp hX hFw hR hub hg s
    have hne : X.tr g ≠ [] := by
      intro h
      simp [h] at hb0
    exact (svDone_lag hp hX hFw hub (g / L.block) s).blk hX hub hg ⟨_, _, _, _, hn⟩ hne
      ⟨hyP, by omega⟩ hyt (by rw [hyP.1]) (by omega)
  · exact .inl ⟨.commit, by simp, hall⟩

/-- **Warpgroup 0's wait on `svDone s` is blocked**, when the object's records do not fault: by
an undelivered commit notification, or by the CTA's MMA producer short of the slot's uses. -/
theorem svDone_w0Blk (hub : ¬ HasUb X) {g q : Nat} {s : Fin 2} {sc : MbarScope}
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.svDone s)), r.fault = none)
    (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨1184, .wait (MbarRow.loc L g (.svDone s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.svDone s)) q := by
  simp only [MbarRow.loc] at hff hn ⊢
  obtain ⟨-, hj, hpq, hwt, hb0⟩ := wg0_svWait hp hX hFw hn
  have hg := hn.lt
  have hR1 := blocksOf_pos hp (g / L.block)
  have N := svDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) (g / L.block) s
  have hb0' : 0 < ((X.tr g).take (X.tr g).length).countP isBar0 := by
    rw [List.take_length]
    exact hb0
  obtain ⟨st, hst⟩ := Unit.final_of_init hX N.init N.noInval
    (objects_ne hp hX hFw hI hg (.inr ⟨rfl, hrel⟩) hb0' (.svDone s))
  refine ⟨st, hst, fun hpar => ?_⟩
  have hU : ringUses 2 s.val (blocksOf P L (g / L.block)) =
      (blocksOf P L (g / L.block) - 1) / 2 + 1 := by
    rw [hj]
    simp only [MbarRow.slot2, ringUses]
    omega
  have hne : X.tr g ≠ [] := by
    intro h
    simp [h] at hb0
  obtain ⟨y, hyt, hyP, hCy⟩ := prod_le hp hX hFw hR hub hg s
  by_cases hshort : (X.tr y).countP (commitsTo (mbarLoc L (g / L.block) (.svDone s))) <
      ringUses 2 s.val (blocksOf P L (g / L.block))
  · refine Sched.blk_of_lagsN hX hub hg hne hyt (by rw [hyP.1]) fun _ => ⟨fun k pc hx => ?_, ?_⟩
    · obtain ⟨hyc, -, ⟨hnx, -⟩ | ⟨k0, e0, he0, hu0, hon⟩⟩ := hyP
      · exact hnx k pc hx
      · have := mma_svExit hp hX hFw he0 hu0 hon hyc hx (j := s)
        omega
    · have hlt := sv_lt_w0 _ hR1
      have hlast : 2 * ((blocksOf P L (g / L.block) - 1) / 2) + s.val =
          blocksOf P L (g / L.block) - 1 := by
        rw [hj]
        simp only [MbarRow.slot2]
        omega
      obtain ⟨hyc, -, ⟨-, ht⟩ | ⟨k0, e0, he0, hu0, hon⟩⟩ := hyP
      · have := elect_lt (blocksOf P L (g / L.block) - 1) (mmaOff + mmaPvc)
        simp only [svCommit] at hlt
        omega
      · have h1 := mma_svEarly hp hX hFw hub he0 hu0 hon hyc hshort
        have h2 := svCommit_mono (a := 2 * (X.tr y).countP
          (commitsTo (mbarLoc L (g / L.block) (.svDone s))) + s.val)
          (b := blocksOf P L (g / L.block) - 1) (by omega)
        omega
  by_cases hall : ∀ i sp rank m', X.Commit i sp → TcCommit.target sp rank = some m' →
      rank ∈ X.tcNotified i
  · have hge := phase_ge hp hX hFw hR hI hB (g / L.block) s hff hall hst
    have hle := N.phase_le_commit_count hX hst
    have hmax := mma_svCommits_le hp hX hFw (y := mmaLane L X (g / L.block)) (g / L.block) s
    omega
  · exact .inl ⟨.commit, by simp, hall⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

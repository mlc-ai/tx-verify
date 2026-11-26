-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.LagQk
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SvPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Obj
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
import Lemmas.Protocol.UnitNotifyWait
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # Warpgroup 0's last wait on `svDone` observes the last commit

Warpgroup 0's one poll of `svDone s` after its last block has the parity of that block's use `u`
(`p % 2 = u % 2`); the parity alone leaves the alias of the commits `u - 2, u - 4, ...`. A path
of the dependency order excludes it: a dequant lane's poll of `svDone s` for use `u` (it observes
the commit `u - 1`) precedes its store and arrival on `dequantReady s`, the MMA lane's poll of
it, the block's QK commit (`mma_qkDq`), warpgroup 0's `qkDone s` poll and its `svDone s` poll.
So the poll's record is after the lane's in the object's history (`not_before_of_reach`), the
phase it observes is above the phase of the commit `u - 1`, and with at most `u + 1` commits it
is the phase of the commit `u` (`svDone_final`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **The last poll of `svDone s` observes the notification of the commit `u`**: a poll of
warpgroup-0 lane `b` with parity `u % 2` after `u + 1` polls of `qkDone s`, the MMA lane making at
most `u + 1` commits to `svDone s`. -/
theorem svDone_final {c jw pc p u : Nat} {s : Fin 2} {b : Fin 128} {acq : Bool} {sc : MbarScope}
    (hw : X.get (wg0Lane L c b, jw) =
      some ⟨pc, .wait (mbarLoc L c (.svDone s)) p true acq sc⟩)
    (hq : okPolls (mbarLoc L c (.qkDone s)) ((X.tr (wg0Lane L c b)).take jw) = u + 1)
    (hpar : p % 2 = u % 2)
    (hmax : (X.tr (mmaLane L X c)).countP (commitsTo (mbarLoc L c (.svDone s))) ≤ u + 1) :
    ∃ i pc' sp rank, X.get (mmaLane L X c, i) = some ⟨pc', .tc (.commit sp)⟩ ∧
      sp.mbar = mbarLoc L c (.svDone s) ∧
      TcCommit.target sp rank = some (mbarLoc L c (.svDone s)) ∧
      ((X.tr (mmaLane L X c)).take i).countP (commitsTo (mbarLoc L c (.svDone s))) = u ∧
      rank ∈ X.tcNotified (mmaLane L X c, i) ∧
      WaitObserves X (.async (mmaLane L X c, i) (.tcNotify rank)) (wg0Lane L c b, jw)
        (mbarLoc L c (.svDone s)) acq sc := by
  have O := svDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s
  obtain ⟨k, r, st, hr, hid, -, hwt, hst, hpp, hcomp⟩ := O.wait_rec hX hw
  have hlen : k ≤ (X.objects (mbarLoc L c (.svDone s))).length :=
    (List.getElem?_eq_some_iff.mp hr).1.le
  -- the observed phase holds no commit below `u`
  have hlow : 0 < st.phase ∧ ∀ x ∈ Notify.S X (mbarLoc L c (.svDone s)) (mmaLane L X c)
      (mbarLoc L c (.svDone s)), Notify.ph X (mbarLoc L c (.svDone s)) (mmaLane L X c)
        (mbarLoc L c (.svDone s)) x = st.phase - 1 → u ≤ x.2 := by
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · exact ⟨by omega, fun _ _ _ => Nat.zero_le _⟩
    obtain ⟨jq, pcq, pq, acqq, scq, hjq, hgq, hqq⟩ := UnitHandoff.exists_poll (c := u) hq.ge
    obtain ⟨ic, pci, spq, rankq, hgc, hmq, htq, hcq, hWq⟩ :=
      (qkDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s).observes_witness hX
        (qkReach hp hX hFw hR hI hB c s b) hgq (by simpa using hqq)
    have hlt := mma_qkDq hp hX hFw (mma_commit_warp hp hX hFw hgc) hgc hmq
    rw [hcq] at hlt
    let D := dqSlot hp hX hFw hR hI hB hN c s
    let RR := D.ring hX
    have hil : ic < (X.tr (mmaLane L X c)).length := (List.getElem?_eq_some_iff.mp hgc).1
    let a0 : Fin 128 := ⟨0, by decide⟩
    obtain ⟨hPres, hPath⟩ := RR.reach_consumer_op hX.depAcyclic a0 (b := (0 : Fin 1)) (t := u)
      (op := (mmaLane L X c, ic)) (fun j hj => Poll.guard D.spins hil (Nat.lt_of_le_of_lt hj hlt))
      hu le_rfl
    have hpd : u < okPolls (mbarLoc L c (.svDone s)) (X.tr (deqLane L c a0)) :=
      Poll.nth_present.mp hPres
    have hsel : 4 ≤ MbarRow.warp L (deqLane L c a0) := by have := deqLane_warp hp c a0; omega
    obtain ⟨kd, wd, std, hkd, hidd, -, -, hstd, hposd, -, hoo⟩ := O.poll_obs hX hu hpd hsel
    obtain ⟨pcd, pd, acqd, scd, hgd, hcd⟩ := Poll.nth_spec hpd
    obtain ⟨kd', rd, std', hkd', hidd', -, -, hstd', hppd, -⟩ := O.wait_rec hX hgd
    obtain rfl : kd = kd' := ObjectInit.checked_record_index_eq (X.objects_checked hX _) hkd hkd'
      (hidd.trans hidd'.symm)
    obtain rfl : std = std' := Option.some.inj (hstd.symm.trans hstd')
    have hpard := O.parityOf hsel hgd
    rw [hcd] at hpard
    have hIss : DepStep L kernel X (.thread (mmaLane L X c, ic), false)
        (.async (mmaLane L X c, ic) (.tcNotify rankq), false) :=
      DepStep.issue ⟨_, hgc⟩ (Witness.waitObserves_tcNotify hWq hgq).1 (fun _ h => by cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    have hjwl : jw < (X.tr (wg0Lane L c b)).length := (List.getElem?_eq_some_iff.mp hw).1
    have hRes : Resumes kernel X (wg0Lane L c b, jq) (wg0Lane L c b, jw) := by
      have h := Poll.guard (K := kernel) (X := X) (fun _ _ _ _ _ _ he => poll_canonical hX he)
        hjwl (n := u) (m := mbarLoc L c (.qkDone s)) (by omega)
      rwa [show Poll.nth X (mbarLoc L c (.qkDone s)) (wg0Lane L c b) u = jq by
        rw [← hqq]; exact Poll.nth_eq hgq] at h
    have hdep := ((hPath.tail hIss).tail (DepStep.of_witness L hWq)).tail
      (DepStep.of_resumes L hRes)
    have hBefore := MbarRing.Round.Slot.not_before_of_reach
      (m := mbarLoc L c (.svDone s)) hX hdep
    have hIdx : kd ≤ k := by
      by_contra hlt'
      exact hBefore ⟨k, kd, r, wd, hr, hid, hkd, hidd, Nat.lt_of_not_le hlt'⟩
    obtain ⟨adv, hAdv, hLe⟩ := (X.objects_checked hX _).phase_mono O.noInval hIdx hlen hstd
    obtain rfl : adv = st := (Option.some.inj (hAdv.symm.trans hst))
    have hlts : std.phase < adv.phase := by omega
    refine ⟨by omega, fun x hx hph => ?_⟩
    by_contra hlx
    have hlx : x.2 + 1 ≤ u := by omega
    obtain ⟨-, hphx⟩ := (RR.content_empty hX.depAcyclic (a := a0) (n := x.2)
      (by
        rcases Nat.lt_or_eq_of_le hlx with h | h
        · exact (RR.ltE a0 (x.2 + 1) u (by omega) h hPres).1
        · rw [h]; exact hPres)).2 (0 : Fin 1)
    have hoe : RR.oE a0 (x.2 + 1) ≤ RR.oE a0 u := by
      rcases Nat.lt_or_eq_of_le hlx with h | h
      · exact (RR.ltE a0 (x.2 + 1) u (by omega) h hPres).2.le
      · rw [h]
    have hxe : Notify.ph X (mbarLoc L c (.svDone s)) (mmaLane L X c) (mbarLoc L c (.svDone s)) x =
        RR.phE a0 (0, x.2) := rfl
    have hou : RR.oE a0 u = std.phase - 1 := hoo
    omega
  obtain ⟨hpos, hge⟩ := hlow
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (O.card_of_state hX hlen hst hpos)
  obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, pcx, sp, hget, hm0, ht, hcnt⟩ := O.S_rec hxS
  have hle : x.2 ≤ u := by
    have h1 := countP_take_succ (p := commitsTo (mbarLoc L c (.svDone s))) hget
      (by simp [commitsTo, hm0])
    have h2 := (List.take_sublist (Notify.cm X (mmaLane L X c) (mbarLoc L c (.svDone s)) x.2 + 1)
      (X.tr (mmaLane L X c))).countP_le (p := commitsTo (mbarLoc L c (.svDone s)))
    omega
  have hxu : x.2 = u := le_antisymm hle (hge x hxS hxp)
  have hcomp' : r.reply.completed = some (st.phase - 1) := by
    simp only [hcomp, hpos, ↓reduceIte]
  have hWit := O.wait_witness hX hxS hr hid hwt hcomp' hxp
  obtain ⟨hrank, hwo⟩ := Witness.waitObserves_tcNotify hWit hw
  exact ⟨_, pcx, sp, _, hget, hm0, ht, hcnt.trans hxu, hrank, hwo⟩

/-- **A warpgroup-0 poll at pc 1184 observes the MMA lane's last commit**: the poll (of a lane
of warpgroup 0, pc 1184, on `svDone s` of CTA `c`) is on the slot of the CTA's last block and
observes the notification of the lane's commit with `(R - 1) / 2` earlier ones to it. -/
theorem svDone_last {c y jw p : Nat} {s : Fin 2} {acq : Bool} {sc : MbarScope}
    (hy : MbarRow.warp L y < 4)
    (he : X.get (y, jw) = some ⟨1184, .wait (mbarLoc L c (.svDone s)) p true acq sc⟩) :
    s = MbarRow.slot2 (blocksOf P L c - 1) ∧ ∃ ic pci spi rank,
      X.get (mmaLane L X c, ic) = some ⟨pci, .tc (.commit spi)⟩ ∧
      spi.mbar = mbarLoc L c (.svDone s) ∧
      TcCommit.target spi rank = some (mbarLoc L c (.svDone s)) ∧
      ((X.tr (mmaLane L X c)).take ic).countP (commitsTo (mbarLoc L c (.svDone s))) =
        (blocksOf P L c - 1) / 2 ∧
      rank ∈ X.tcNotified (mmaLane L X c, ic) ∧
      WaitObserves X (.async (mmaLane L X c, ic) (.tcNotify rank)) (y, jw)
        (mbarLoc L c (.svDone s)) acq sc := by
  obtain ⟨hc, hs, hpar, hq, -⟩ := wg0_svPoll hp hX hFw he
  obtain ⟨b, hb⟩ := wg0_lane hp (g := y) (pc := 1184) ⟨hy, by omega, by omega⟩
  rw [hc] at hb
  subst hb hs
  have hmax : (X.tr (mmaLane L X c)).countP
      (commitsTo (mbarLoc L c (.svDone (MbarRow.slot2 (blocksOf P L c - 1))))) ≤
        (blocksOf P L c - 1) / 2 + 1 := by
    refine (mma_svCommits_le hp hX hFw (y := mmaLane L X c) c _).trans ?_
    simp only [MbarRow.slot2, ringUses]
    omega
  obtain ⟨ic, pci, spi, rank, hgc, hmi, hti, hci, hrk, hobs⟩ :=
    svDone_final hp hX hFw hR hI hB hN he hq hpar hmax
  exact ⟨rfl, ic, pci, spi, rank, hgc, hmi, hti, hci, hrk, hobs⟩

/-- **Every MMA and copy of the MMA lane is done at warpgroup 0's poll at pc 1184**: the poll
(of a lane of warpgroup 0, pc 1184, on `svDone s` of CTA `c`) observes the notification of the
lane's last commit to it, which tracks every MMA and copy before it (`mma_asyncSv`). -/
theorem svDone_done {c y jw pc0 i0 : Nat} {s : Fin 2} {p : Nat} {sc : MbarScope}
    {k : TcKind} (hy : MbarRow.warp L y < 4) (hmc : mmaLane L X c / L.block = c)
    (he : X.get (y, jw) = some ⟨1184, .wait (mbarLoc L c (.svDone s)) p true true sc⟩)
    (hg0 : X.get (mmaLane L X c, i0) = some ⟨pc0, .tc k⟩)
    (hat : MbarRow.MmaAt L (mmaLane L X c) pc0) (h1853 : 1853 < pc0)
    (hk : (∃ b sp acc mask, k = .mma b sp acc mask) ∨ ∃ cs, k = .cp cs) :
    AsyncObserved X (mmaLane L X c, i0) .mmaDone (y, jw) true sc ∧
      X.AsyncPresent (mmaLane L X c, i0) .mmaDone := by
  obtain ⟨hs, ic, pci, spi, rank, hgc, hmi, hti, hci, hrk, hobs⟩ :=
    svDone_last hp hX hFw hR hI hB hN hy he
  subst hs
  have hle := mma_asyncSv hp hX hFw (y := mmaLane L X c) hg0 hat h1853
    (by rcases hk with ⟨b', sp', a', m', h⟩ | ⟨cs, h⟩ <;> subst h <;> simp)
  rw [hmc] at hle
  have hlt : i0 < ic := by
    by_contra hge
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with h1 | rfl
    · have e1 := countP_take_succ (p := commitsTo (mbarLoc L c (.svDone
        (MbarRow.slot2 (blocksOf P L c - 1))))) hgc (by simp [commitsTo, hmi])
      have e2 := countP_take_mono (commitsTo (mbarLoc L c (.svDone
        (MbarRow.slot2 (blocksOf P L c - 1))))) (X.tr (mmaLane L X c)) (show ic + 1 ≤ i0 by omega)
      omega
    · rw [hg0] at hgc
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq] at hgc
      obtain ⟨-, rfl⟩ := hgc
      rcases hk with ⟨_, _, _, _, h⟩ | ⟨_, h⟩ <;> cases h
  have htr : TracksMma X (mmaLane L X c, i0) (mmaLane L X c, ic) := by
    refine ⟨rfl, hlt, ?_, spi, pci, hgc⟩
    rcases hk with ⟨b', sp', a', m', h⟩ | ⟨cs, h⟩ <;> subst h
    · exact .inl ⟨b', sp', a', m', pc0, hg0⟩
    · exact .inr (.inl ⟨cs, pc0, hg0⟩)
  exact ⟨⟨_, _, ⟨(mmaLane L X c, ic), spi, rank, rfl, htr, ⟨pci, hgc⟩, hti, hrk⟩, hobs⟩,
    (hX.tcCommit _ rank hrk).2 _ htr⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

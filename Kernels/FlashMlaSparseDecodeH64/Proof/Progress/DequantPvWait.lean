-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.SoftmaxPvWait
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarPublished
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Lemmas.Protocol.NotifyBlocker

public section

/-! # A blocked dequantization reuse wait requires an earlier PV issue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow AsyncCopy MBarrier Protocol GemmRing PTX.MbarRing
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

private theorem reuse_state (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg2.D} (hg : g < L.threads)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg2 d))) :
    let m := empty L (ctaOf L g) (rawSlot d.block)
    ∃ st, stateBefore (X.objects m) (X.objects m).length = some st := by
  let slot := rawSlot d.block
  let entry (s : Fin 2) : Fin 23 := if s.val = 0 then 8 else 14
  have hLoc (s : Fin 2) :
      IndexRing.initTable.loc L (ctaOf L g) (entry s) = empty L (ctaOf L g) s := by
    fin_cases s <;> rfl
  obtain ⟨i, hi⟩ := MachineTracking.table_init_of_followed_tail
    hpre hX hs hg hd (by simp) (entry slot)
  rw [hLoc slot] at hi
  obtain ⟨r, hFirst, _, hAct, hClean⟩ := Safety.mbar_init_record_first hpre hX hs ht hi
  have hPos := (List.getElem?_eq_some_iff.mp hFirst).1
  obtain ⟨st, hState, _⟩ := ObjectInit.checked_expected_after_init (X.objects_checked hX _)
    (fun _ hr => Safety.mbar_record_not_inval hX hr) hFirst hAct hClean hPos le_rfl
  exact ⟨st, hState⟩

variable (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hsg : SyncGuarded L kernel X) {g : Nat} {d : Wg2.D} (hp : PendingState P L X g (.wg2 d))
include hpre hmax hs ht hsg hp

/-- A maximal prefix blocked on dequantization storage reuse lacks the preceding PV issue.
The first use can always acquire the initially free slot. -/
theorem pending_dequant_pv_missing (hRel : PTX.Step.Released L X g) (hd : d.site = .svDone) :
    let m := empty L (ctaOf L g) (rawSlot d.block)
    ∃ issuer, MmaIssuer P L X (ctaOf L g) issuer ∧
      (X.tr issuer).countP (commitsTo m) < d.block / 2 := by
  have hX := hmax.1
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := empty L cta slot
  let n := d.block / 2
  let sound := fun h hh => (hs h hh).machine
  have hHub := Safety.no_ub hpre hX hs ht
  obtain ⟨_, hRun⟩ := Frame.run_some hX hHub hp.1
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1.1 hRun hp.2
  have hInv : Wg2.Inv P L g d := hInv
  obtain ⟨st, hState⟩ := reuse_state hpre hX hs ht hp.1.1 hp.2
  have hObj : (DequantWait.pv).object L g d = m := by
    change (⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff d.buf⟩ : Loc) = m
    rw [hInv.bufBlock]
    rfl
  have hParity : st.phase % 2 = (1 - n % 2) % 2 := by
    by_contra hn
    apply hmax.not_grows
    refine dequant_poll_extension (w := .pv) (before := st) hpre hs hX hHub hp.1 hRel hp.2 hd ?_ ?_
    · rwa [hObj]
    · simpa only [DequantWait.parity, hInv.parBlock, n] using hn
  have hG : wgOf L g = 2 := RingRoleGeometry.of_trace hX hp.1.1 (sound g hp.1.1) hp.2
  obtain ⟨lane, hLane⟩ := RawRing.consumer_of_wg2 hpre (cta := cta) rfl hG
  change g = producer L cta lane at hLane
  obtain ⟨issuer, hIssuer⟩ := exists_issuer (cta := cta) hpre hX sound
  let R := dequantRing (slot := slot) hpre hX sound hIssuer
  let O := reuse_obj (slot := slot) hpre hX sound hIssuer
  have hCount := Wg2GemmTrace.composed_reuse_count hpre
    ((sound g hp.1.1).produces (hX.thr g hp.1.1)) hp.2 hd
  rw [List.take_length] at hCount
  change PTX.Flow.okPolls m (X.tr g) = n at hCount
  have hBound : (X.tr issuer).countP (commitsTo m) ≤ n := by
    by_contra! hLong
    obtain ⟨⟨tag, kind⟩, he, htick, ho⟩ := nthEv_spec hLong
    obtain ⟨sp, hk, hm⟩ := Notify.commit_of_commitsTo htick
    change kind = _ at hk
    subst kind
    have hi : X.Commit (issuer, Notify.cm X issuer m n) sp := ⟨tag, he⟩
    have hTarget : TcCommit.target sp 0 = some m := by rw [commit_target hpre hX hs ht hi, hm]; rfl
    have hGuard := guard_pv_issue hpre hX sound he hTarget (show n ≤ _ from ho.symm.le)
    have hPoll := MbarRing.Round.Slot.present_of_guard hGuard
    change X.RefPresent (.thread (R.wF 0 n)) at hPoll
    obtain ⟨hx, _⟩ := R.observes_full hX.depAcyclic hPoll lane
    change (lane, n) ∈ Unit.S X (full L cta slot) (producer L cta) at hx
    have hReady := guard_ready (n := n) hpre hX sound hx le_rfl
    have hSeen := Poll.nth_present.mp (MbarRing.Round.Slot.present_of_guard hReady)
    change n < PTX.Flow.okPolls m (X.tr (producer L cta lane)) at hSeen
    rw [← hLane, hCount] at hSeen
    exact (Nat.lt_irrefl n hSeen)
  refine ⟨issuer, hIssuer, ?_⟩
  by_contra! hEnough
  have hRecords (j : Nat) (hj : j < n) :
      ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
        r.id = Notify.it X m issuer m j ∧ countedArrive r = true := by
    obtain ⟨⟨tag, kind⟩, he, tick, _⟩ := nthEv_spec (hj.trans_le hEnough)
    obtain ⟨sp, hk, hm⟩ := Notify.commit_of_commitsTo tick
    change kind = _ at hk
    subst kind
    have hi : X.Commit (issuer, Notify.cm X issuer m j) sp := ⟨tag, he⟩
    have hTgt : TcCommit.target sp 0 = some m := by rw [commit_target hpre hX hs ht hi, hm]; rfl
    have hNotified := completed_commit_notified hpre hmax hs ht hi hTgt
      (fun _ hTrack => issued_tc_completed hpre hmax hs ht hsg hTrack.2.2.1)
    exact Notify.Obj.notified_rec_of_rank hX (Safety.sv_done_fault_free hpre hX sound ht)
      he hTgt hNotified
  have hLower := O.phase_ge_of_records hX hState hEnough hRecords
  have hUpper := (O.phase_le_commit_count hX hState).trans hBound
  omega

omit hpre hmax hs ht hsg hp in
private theorem mma_before_dequant_reuse {g h : Nat} {d : Wg2.D} {q : Wg1Mma.D}
    (hd : d.site = .svDone) (hOut : q.site ≠ .outBar) (hExit : q.site ≠ .exit)
    (hBlock : q.i < d.block) :
    priority P L h (.mma q) < priority P L g (.wg2 d) := by
  cases hSite : q.site
  all_goals try exact (hOut hSite).elim
  all_goals try exact (hExit hSite).elim
  all_goals
    simp only [priority, matmulTime, quantTime, hSite, hd, wg2Ordinal, mmaOrdinal, blockTime]
    omega

/-- A blocked reuse poll has an earlier pending MMA lane of the same CTA. -/
theorem pending_dequant_pv_earlier (hRel : PTX.Step.Released L X g) (hd : d.site = .svDone) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.wg2 d) := by
  obtain ⟨issuer, hIssuer, hShort⟩ := pending_dequant_pv_missing hpre hmax hs ht hsg hp hRel hd
  let prior := d.block - 2
  have hN : 2 ≤ d.block := by omega
  have hSlot : rawSlot prior = rawSlot d.block := Fin.ext (by
    change (d.block - 2) % 2 = d.block % 2
    omega)
  have hPrevious : (X.tr issuer).countP (commitsTo (empty L (ctaOf L g) (rawSlot prior))) ≤
      prior / 2 := by
    rw [hSlot]
    dsimp only [prior]
    omega
  have hHub := Safety.no_ub hpre hmax.1 hs ht
  obtain ⟨_, hRun⟩ := Frame.run_some hmax.1 hHub hp.1
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1.1 hRun hp.2
  have hInv : Wg2.Inv P L g d := hInv
  have hBlock := hInv.block
  rw [hInv.len0, hInv.len1] at hBlock
  change d.block < Wg0.blocksOf P L g at hBlock
  have hEarlier : prior < d.block := by dsimp [prior]; omega
  obtain ⟨h, q, hCta, hPending, hBefore⟩ :=
    pending_mma_before_unissued_pv hpre hmax.1 hs ht hp.1.1
      (hEarlier.trans hBlock) hIssuer hPrevious
  refine ⟨h, q, hCta, hPending, ?_⟩
  cases hBefore with
  | launch s =>
    simp only [priority, quantTime, hd, wg2Ordinal, blockTime]
    omega
  | dispatch =>
    simp only [priority, quantTime, hd, wg2Ordinal, blockTime]
    omega
  | mma p hOut hExit hLt => exact mma_before_dequant_reuse hd hOut hExit (hLt.trans_lt hEarlier)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

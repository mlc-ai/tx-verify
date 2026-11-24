-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarUnitFaults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0GemmPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarPublished
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Lemmas.Protocol.NotifyBlocker

public section

/-! # A blocked softmax QK wait identifies an unissued or undelivered commit -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow AsyncCopy MBarrier Protocol GemmRing PTX.MbarRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

private theorem qk_wait_state (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg0.D} (hg : g < L.threads)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d))) :
    let m := qk L (ctaOf L g) (rawSlot d.block)
    ∃ st, stateBefore (X.objects m) (X.objects m).length = some st := by
  let slot := rawSlot d.block
  let entry (s : Fin 2) : Fin 23 := if s.val = 0 then 6 else 12
  have hLoc (s : Fin 2) :
      IndexRing.initTable.loc L (ctaOf L g) (entry s) = qk L (ctaOf L g) s := by
    fin_cases s <;> rfl
  obtain ⟨i, hi⟩ := MachineTracking.table_init_of_followed_tail
    hpre hX hs hg hd (by simp) (entry slot)
  rw [hLoc slot] at hi
  obtain ⟨r, hFirst, _, hAct, hClean⟩ := Safety.mbar_init_record_first hpre hX hs ht hi
  have hPos := (List.getElem?_eq_some_iff.mp hFirst).1
  obtain ⟨st, hState, _⟩ := ObjectInit.checked_expected_after_init (X.objects_checked hX _)
    (fun _ hr => Safety.mbar_record_not_inval hX hr) hFirst hAct hClean hPos le_rfl
  exact ⟨st, hState⟩

/-- A maximal execution with a pending QK wait either lacks that generation's commit or has
issued it without the notification. Every earlier notification in this slot has been observed. -/
theorem pending_softmax_qk_missing (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg0.D} (hp : PendingState P L X g (.wg0 d)) (hRel : PTX.Step.Released L X g)
    (hd : d.site = .qkDone) :
    let m := qk L (ctaOf L g) (rawSlot d.block)
    ∃ issuer, MmaIssuer P L X (ctaOf L g) issuer ∧
      ((X.tr issuer).countP (commitsTo m) ≤ d.block / 2 ∨
        ∃ sp, X.Commit (issuer, Notify.cm X issuer m (d.block / 2)) sp ∧
          TcCommit.target sp 0 = some m ∧
          0 ∉ X.tcNotified (issuer, Notify.cm X issuer m (d.block / 2))) := by
  classical
  have hX := hmax.1
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := qk L cta slot
  let n := d.block / 2
  let sound := fun h hh => (hs h hh).machine
  obtain ⟨st, hState⟩ := qk_wait_state hpre hX hs ht hp.1.1 hp.2
  have hEq : (SoftmaxGemmWait.qk).object L g d.block = m := rfl
  have hParity : st.phase % 2 = n % 2 := by
    by_contra hn
    apply hmax.not_grows
    apply softmax_gemm_poll_extension hpre hs hX (Safety.no_ub hpre hX hs ht)
      hp.1 hRel hp.2 .qk hd _ hn
    rwa [hEq]
  have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hp.1.1 (sound g hp.1.1) hp.2
  obtain ⟨lane, hLane⟩ := softmax_thread hpre (cta := cta) rfl hWg
  obtain ⟨issuer, hIssuer⟩ := exists_issuer (cta := cta) hpre hX sound
  let R := scoreRing (slot := slot) hpre hX sound ht hIssuer
  let O := qk_obj (slot := slot) hpre hX sound ht hIssuer
  have hCount := Wg0GemmTrace.composed_qk_counts hpre
    ((sound g hp.1.1).produces (hX.thr g hp.1.1)) hp.2 hd
  rw [List.take_length] at hCount
  change PTX.Flow.okPolls m (X.tr g) = n at hCount
  have hReach : Notify.Reach L kernel Assumptions.all X m issuer m 0 g := by
    intro x hx j hj
    have hPath := (R.reach hX.depAcyclic).1 0 x hx lane j hj
    change Relation.TransGen (DepStep L kernel X)
      (.thread (softmax L cta lane, Poll.nth X m (softmax L cta lane) j), true)
      (Notify.it X m issuer m x.2, false) at hPath
    rw [← hLane] at hPath
    exact hPath
  have hLe := O.phase_le hX hReach hState
  rw [hCount] at hLe
  have hPhase : st.phase ≤ n := by omega
  refine ⟨issuer, hIssuer, ?_⟩
  by_cases hCommits : n < (X.tr issuer).countP (commitsTo m)
  · right
    obtain ⟨⟨tag, kind⟩, he, tick, _⟩ := nthEv_spec hCommits
    obtain ⟨sp, hk, hm⟩ := Notify.commit_of_commitsTo tick
    change kind = _ at hk
    subst kind
    have hi : X.Commit (issuer, Notify.cm X issuer m n) sp := ⟨tag, he⟩
    have hTarget : TcCommit.target sp 0 = some m := by rw [commit_target hpre hX hs ht hi, hm]; rfl
    refine ⟨sp, hi, hTarget, ?_⟩
    intro hNotified
    have hClean := Safety.qk_done_fault_free hpre hX sound ht (cta := cta) (slot := slot)
    have hRecords (j : Nat) (hj : j < n + 1) :
        ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
          r.id = Notify.it X m issuer m j ∧
          countedArrive r = true := by
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj' | rfl
      · have hPresent : X.RefPresent (.thread (R.wF lane j)) := by
          change X.RefPresent (.thread (softmax L cta lane, Poll.nth X m (softmax L cta lane) j))
          rw [← hLane]
          exact Poll.nth_present.mpr (hCount.symm ▸ hj')
        obtain ⟨hS, _⟩ := R.observes_full hX.depAcyclic hPresent 0
        obtain ⟨⟨k, r, hk, hId, hFault, hAct⟩, _⟩ := O.S_rec hS
        exact ⟨k, r, hk, hId, countedArrive_iff.mpr ⟨hFault, 1, 0, hAct⟩⟩
      · exact Notify.Obj.notified_rec_of_rank hX hClean he hTarget hNotified
    have hBound := O.phase_ge_of_records hX hState hCommits hRecords
    omega
  · exact .inl (Nat.le_of_not_gt hCommits)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

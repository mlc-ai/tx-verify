-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Tcgen05.TcNotifyConsistent
import Lemmas.Step.Object
import Lemmas.Tcgen05.MmaComplete
import Lemmas.Kernel.ProgressDescent

public section

/-! # Progress of a Tensor Core commit whose operations have completed -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow AsyncCopy _root_.PTX.MBarrier PTX.Step

/-- When an operation has captured its operands and its arithmetic predecessors have completed,
recording its completion preserves the FlashMLA assumptions. -/
theorem tc_completion_extension {L : Launch} {mem0 : Mem0} {X : Execution} {i : EvId}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : X.async.mmaStarted i = true) (hn : X.async.mmaDone i = false)
    (hready : TcMma.CompletionReady L X i) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨values, hv⟩ : ∃ values, X.async.mmaOperands i = some values := by
    cases hh : X.async.mmaOperands i with
    | none => simp [Snapshot.mmaStarted, hh] at hs
    | some values => exact ⟨values, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, X.get i = some e := by
    rcases hX.tma.2.1.1 i hs with ⟨_, _, _, _, _, ⟨_, he⟩, _⟩ |
      ⟨_, _, ⟨_, he⟩, _⟩ | ⟨_, _, ⟨_, he⟩, _⟩
    all_goals exact ⟨_, he⟩
  have hle := X.le_completeMma i
  refine ⟨_, consistent_completeMma hX hs hn hready
    (Interface.all_wf_effects hX hle rfl rfl rfl), hle, ?_⟩
  exact completeMma_size hv (Frame.lt_of_get hX he) (len_of_get he) hn

/-- A commit with completed operations can add its pending notification. Appending the
notification preserves the thread traces and assumptions when a selected preceding commit
has already notified the same rank. -/
theorem commit_notification_extension {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {s : TcCommit.Spec} {m : Loc} {rank : Fin 16}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : X.Commit i s) (htarget : TcCommit.target s rank = some m)
    (hn : rank ∉ X.tcNotified i)
    (hd : ∀ x, TracksMma X x i → X.async.mmaDone x = true)
    (hPrev : ∀ (j tag : Nat) (sp : TcCommit.Spec),
      X.get (i.1, j) = some ⟨tag, .tc (.commit sp)⟩ →
      Assumptions.commitOrder.commitInOrder tag = true → j < i.2 →
      (∀ k, j < k → k < i.2 → ¬ ∃ s, X.Commit (i.1, k) s) →
      rank ∈ X.tcNotified (i.1, j)) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨last, hlast⟩ := (hX.tma.2.2.1 m).1.2
  let record : Record Ref := checkedRecord (.async i (.tcNotify rank)) (.arrive 1 0) last
  have hid : record.id = .async i (.tcNotify rank) := checkedRecord_id ..
  have ha : record.action = .arrive 1 0 := checkedRecord_action ..
  have hchecked : CheckedLog (X.objects m ++ [record]) := by
    apply CheckedLog.snoc hlast (hX.tma.2.2.1 m).1.1
    · intro hmem
      obtain ⟨r, hr, he⟩ := List.mem_map.mp hmem
      exact no_tc_notification_record hX.tma.2.2.1 hn hr (he.trans hid)
    · exact checkedRecord_ok ..
  have hle := X.le_notifyTcRecord i rank m record
  have hOrder : X.NotifiedInOrder Assumptions.commitOrder.commitInOrder
      (X.notifyTcRecord i rank m record) := by
    intro e r hr hNew j tag sp hGet hSel hJ hBetween
    have hId : e = i ∧ r = rank := by
      change r ∈ (if e = i then insert rank (X.tcNotified e) else X.tcNotified e) at hr
      split_ifs at hr with he
      · rcases Finset.mem_insert.mp hr with h | h
        · exact ⟨he, h⟩
        · exact (hNew h).elim
      · exact (hNew hr).elim
    obtain ⟨rfl, rfl⟩ := hId
    have hOld := hPrev j tag sp hGet hSel hJ hBetween
    exact hle.2.2.2.2.2.2.2.2.2.2.2.2 _ hOld
  have hconsistent := consistent_notifyTcRecord hX hi htarget hn hd hid ha hchecked
    (Interface.all_wf_effects_inOrder hX hle rfl rfl hOrder)
  exact ⟨_, hconsistent, hle,
    notifyTcRecord_size (Frame.lt_of_get hX hi.choose_spec) (len_of_get hi.choose_spec) hn⟩

/-- Every actual FlashMLA Tensor Core commit notifies its sole local target at rank zero. -/
theorem commit_target {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {sp : TcCommit.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Proof.Machine.code P L g).Sound)
    (ht : Frame.Tracked (Proof.Machine.code P L) X) (hi : X.Commit i sp) :
    ∀ rank, TcCommit.target sp rank = if rank = 0 then some sp.mbar else none := by
  have he := hi.choose_spec
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs i.1 hg).machine he hd
  have hSite := RingCommitEvents.commit_site hf rfl
  cases d
  case mma q =>
    obtain ⟨_, hKind, _, hTarget⟩ := RingCommitEvents.commit_issue hpre hg hSite hf
    obtain rfl := TcKind.commit.inj (Kind.tc.inj hKind)
    exact hTarget
  all_goals exact hSite.elim

/-- A maximal execution has registered each notification whose issues have completed.
At each selected predecessor, the earlier commit tracks only operations of this commit's prefix. -/
theorem completed_commit_notified {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {s : TcCommit.Spec} {m : Loc} {rank : Fin 16}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Proof.Machine.code P L g).Sound)
    (ht : Frame.Tracked (Proof.Machine.code P L) X)
    (hi : X.Commit i s) (htarget : TcCommit.target s rank = some m)
    (hd : ∀ x, TracksMma X x i → X.async.mmaDone x = true) :
    rank ∈ X.tcNotified i := by
  obtain ⟨g, n⟩ := i
  induction n using Nat.strong_induction_on generalizing s m with
  | _ n ih =>
    by_contra hn
    refine hmax.not_grows (commit_notification_extension hmax.1 hi htarget hn hd ?_)
    intro j tag sp hj _ hLt _
    have hRank : rank = 0 := by
      rw [commit_target hpre hmax.1 hs ht hi] at htarget
      split at htarget
      · assumption
      · cases htarget
    have hEarlier : X.Commit (g, j) sp := ⟨tag, hj⟩
    have hTarget' : TcCommit.target sp rank = some sp.mbar := by
      rw [commit_target hpre hmax.1 hs ht hEarlier, ite_eq_left hRank]
    exact ih j hLt (hi := hEarlier) (htarget := hTarget') (hd := fun x hx =>
      hd x ⟨hx.1, hx.2.1.trans hLt, hx.2.2.1, s, hi⟩)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

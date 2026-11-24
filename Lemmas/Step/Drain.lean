-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcCompleteConsistentArbitration
public import Lemmas.Clc.ClcCompleteConsistentWriteWaiting
public import Lemmas.Clc.ClcCompleteConsistentNotifyFrame
public import Lemmas.Clc.ClcCompleteConsistentNotifyWaiting
public import Lemmas.Kernel.ProgressDescent
public import Lemmas.Tcgen05.MmaComplete
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Tcgen05.TcNotifyConsistent
public import Lemmas.Tcgen05.TcNotifyObject

@[expose] public section

/-! # Asynchronous stages a maximal execution has drained

A proof tool for progress, for every kernel. An issued asynchronous stage whose completion
the model allows can be appended as a counted consistent extension, so a maximal execution
contains it. The kernel's assumptions must not constrain the execution (`WfFree`), as for
every assumption that keeps the default well-formedness. Stages whose completion needs
memory or protocol facts (an MMA's operand snapshot, a tensor copy's source, a store's
published sources) take those facts as premises; the kernel's safety layer supplies them.

A tensor-core commit's delivery to a target rank is such a stage. Its premise is the commit's
own delivery rule (`AsyncCopy.CommitOk`): every tracked operation must have completed first.
In a maximal execution, a tracked operation whose operand snapshot (`mmaStarted`) the kernel
supplies has completed; the earlier operations it waits for are derived, not assumed. -/

namespace PTX

open AsyncCopy

noncomputable section

/-- The assumptions put no well-formedness constraint on executions. -/
def Assumption.WfFree (L : Launch) (mem0 : Mem0) (A : List Assumption) : Prop :=
  ∀ a ∈ A, ∀ Y, a.wf L mem0 Y

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem issuer_thread (hX : Consistent L K A mem0 X) {i : EvId} {ev : Event}
    (he : X.get i = some ev) : i.1 < L.threads ∧ i.2 < (X.tr i.1).length := by
  have hlen := len_of_get he
  refine ⟨?_, hlen⟩
  by_contra hno
  rw [hX.outside i.1 (by omega)] at hlen
  simp at hlen

/-! ## Cluster launch control -/

theorem clc_resolve_counted (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    {i : EvId} {s : Clc.Spec} {targets : List Nat} (hi : X.ClcIssue i s targets)
    (hn : (X.clc i).resolved = none) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨hg, hidx⟩ := issuer_thread hX he
  cases hr : X.clcState.response (Clc.requestId i) with
  | none =>
    have hY := consistent_failClc hX ⟨pc, he⟩ hr (fun a ha => hA a ha _)
    have hres : (X.failClc i).clcState.response (Clc.requestId i) = some none :=
      Function.update_self _ _ _
    have hz := consistent_resolveClc_checked hY ⟨pc, he⟩ hn
      (show Clc.Result L i (X.failClc i).clcState (Clc.responseOf L i none) from ⟨none, hres, rfl⟩)
      (fun a ha => hA a ha _)
    refine ⟨_, hz, Execution.le_trans (failClc_le hr) (resolveClc_le hn), ?_⟩
    have hc := resolveClc_size (X := X.failClc i) (r := Clc.responseOf L i none) hg hidx hn
    have hs : (X.failClc i).size L = X.size L := rfl
    omega
  | some answer =>
    have hz := consistent_resolveClc_checked hX ⟨pc, he⟩ hn
      (show Clc.Result L i X.clcState (Clc.responseOf L i answer) from ⟨answer, hr, rfl⟩)
      (fun a ha => hA a ha _)
    refine ⟨_, hz, resolveClc_le hn, ?_⟩
    have hc := resolveClc_size (X := X) (r := Clc.responseOf L i answer) hg hidx hn
    omega

theorem clc_write_counted (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    {i : EvId} {s : Clc.Spec} {targets : List Nat} (hi : X.ClcIssue i s targets) {c : Nat}
    (hc : c ∈ targets) (hn : c ∉ (X.clc i).written) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  cases hr : (X.clc i).resolved with
  | none => exact clc_resolve_counted hA hX hi hr
  | some response =>
    obtain ⟨pc, he⟩ := hi
    obtain ⟨hg, hidx⟩ := issuer_thread hX he
    have hz := consistent_writeClc_checked hX ⟨pc, he⟩ hr hc hn (fun a ha => hA a ha _)
    refine ⟨_, hz, writeClc_le X i c, ?_⟩
    have hcount := writeClc_size (X := X) hg hidx hn
    omega

theorem clc_notify_counted (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    {i : EvId} {s : Clc.Spec} {targets : List Nat} (hi : X.ClcIssue i s targets) {c : Nat}
    (hct : c ∈ targets) (hn : c ∉ (X.clc i).notified) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  by_cases hw : c ∈ (X.clc i).written
  · obtain ⟨pc, he⟩ := hi
    obtain ⟨hg, hidx⟩ := issuer_thread hX he
    let mb : Loc := {s.mbar with cta := c}
    let record := clcCompletionRecord
      (MBarrier.stateBefore (X.objects mb) (X.objects mb).length) i c
    have hid : record.id = .async i (.notify (.cta c)) := clcCompletionRecord_id _ _ _
    have ha : record.action = .completeTx 16 := clcCompletionRecord_action _ _ _
    have hck : MBarrier.CheckedLog (X.objects mb ++ [record]) :=
      notifyClcRecord_checked hX.tma.2.2.1 hn mb
    have hac := (notifyClcRecord_sinkFrame (mb := mb) hX hn hid).orderOk hX.orderOk
    have hz := consistent_notifyClcRecord hX ⟨pc, he⟩ hct hw hn rfl hid ha hck hac
      (fun a ha => hA a ha _)
    have hcount := markClcNotify_size (X := X) (c := c) hg hidx hn
    have hsame : (X.notifyClcRecord i c mb record).size L = (X.markClcNotify i c).size L := rfl
    refine ⟨X.notifyClcRecord i c mb record, hz, notifyClcRecord_le, ?_⟩
    rw [hsame, hcount]
    omega
  · exact clc_write_counted hA hX hi hct hw

/-- A maximal execution has notified every target of every cancellation request. -/
theorem Maximal.clc_notified (hA : Assumption.WfFree L mem0 A)
    (hmax : Maximal L K A mem0 X) {i : EvId} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) : ∀ c ∈ targets, c ∈ (X.clc i).notified := by
  intro c hc
  by_contra hn
  exact (hmax.not_grows (clc_notify_counted hA hmax.1 hi hc hn)).elim

/-! ## Tensor Core MMA -/

/-- A maximal execution has completed every started MMA whose completion is ready. -/
theorem Maximal.mma_done (hA : Assumption.WfFree L mem0 A) (hm : Maximal L K A mem0 X)
    {i : EvId} (hs : X.async.mmaStarted i = true) (hready : TcMma.CompletionReady L X i) :
    X.async.mmaDone i = true := by
  classical
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false =>
    obtain ⟨values, hv⟩ : ∃ values, X.async.mmaOperands i = some values := by
      cases hh : X.async.mmaOperands i with
      | none => simp [Snapshot.mmaStarted, hh] at hs
      | some values => exact ⟨values, rfl⟩
    obtain ⟨ev, hi⟩ : ∃ ev, X.get i = some ev := by
      rcases hm.1.tma.2.1.1 i hs with ⟨d, s, accum, mask, operands, ⟨pc, hi⟩, _⟩ |
        ⟨c, operands, ⟨pc, hi⟩, _⟩ | ⟨s, operands, ⟨pc, hi⟩, _⟩
      · exact ⟨_, hi⟩
      · exact ⟨_, hi⟩
      · exact ⟨_, hi⟩
    obtain ⟨hg, hlen⟩ := issuer_thread hm.1 hi
    have hc := consistent_completeMma hm.1 hs hn hready (fun a ha => hA a ha _)
    have hle := hm.2 _ hc (X.le_completeMma i)
    have hlt := completeMma_size hv hg hlen hn
    omega

/-! ## Tensor Core commit -/

/-- A commit's delivery to a target rank that has not happened can be appended as a counted
consistent extension, once every operation the commit tracks has completed (`hd`, the delivery
rule of `AsyncCopy.CommitOk`). The delivery is an arrival on the target mbarrier whose record
is the actual object transition, so the extension is checked. -/
theorem tc_notify_counted (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some m) (hn : rank ∉ X.tcNotified i)
    (hd : ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaDone x = true) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨hnodup, last, hhistory⟩ := (hX.tma.2.2.1 m).1
  let action := MBarrier.Action.arrive 1 0
  obtain ⟨rec, hid, ha, hok⟩ : ∃ rec : MBarrier.Record AsyncCopy.Ref,
      rec.id = .async i (.tcNotify rank) ∧ rec.action = action ∧ MBarrier.RecordOk last rec := by
    cases hp : MBarrier.perform last action with
    | ok reply =>
      exact ⟨⟨.async i (.tcNotify rank), action, reply, none⟩, rfl, rfl,
        by simp [MBarrier.RecordOk, hp]⟩
    | error err =>
      exact ⟨⟨.async i (.tcNotify rank), action, ⟨last, none, none⟩, some err⟩, rfl, rfl,
        by simp [MBarrier.RecordOk, hp]⟩
  have hfresh : rec.id ∉ (X.objects m).map MBarrier.Record.id := by
    intro hm
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
    exact no_tc_notification_record hX.tma.2.2.1 hn hr (he.trans hid)
  have hchecked := MBarrier.CheckedLog.snoc hhistory hnodup hfresh hok
  obtain ⟨hg, hidx⟩ := issuer_thread hX hi.choose_spec
  exact ⟨X.notifyTcRecord i rank m rec,
    consistent_notifyTcRecord hX hi ht hn hd hid ha hchecked (fun a ha' => hA a ha' _),
    X.le_notifyTcRecord i rank m rec, notifyTcRecord_size hg hidx hn⟩

/-- A maximal execution has delivered every commit's notification to every target rank, given
that every operation the commit tracks has completed (`hready`). That is the commit's own
delivery rule (`AsyncCopy.CommitOk`); `Maximal.commit_notified_of_started` discharges it. -/
theorem Maximal.commit_notified (hA : Assumption.WfFree L mem0 A) (hmax : Maximal L K A mem0 X)
    {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some m)
    (hready : ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaDone x = true) :
    rank ∈ X.tcNotified i := by
  by_contra hn
  exact (hmax.not_grows (tc_notify_counted hA hmax.1 hi ht hn hready)).elim

/-- In a maximal execution every operation a commit tracks has completed, provided each has its
operand snapshot (`mmaStarted`). By induction on the position in the issuing thread: the
operations a tracked MMA waits for (`TcMma.CompletionPrecedes`) are same-thread MMA issues, hence
tracked by the same commit, and have completed by the induction hypothesis. So
`TcMma.CompletionReady` holds and `Maximal.mma_done` applies. -/
theorem Maximal.tracked_mma_done (hA : Assumption.WfFree L mem0 A) (hmax : Maximal L K A mem0 X)
    {i : EvId} {s : TcCommit.Spec} (hi : X.Commit i s)
    (hs : ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaStarted x = true) :
    ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaDone x = true := by
  have key : ∀ n : Nat, ∀ x : EvId, x.2 < n → AsyncCopy.TracksMma X x i →
      X.async.mmaDone x = true := by
    intro n
    induction n with
    | zero => intro x hlt; exact absurd hlt (by omega)
    | succ n ih =>
      intro x hlt hx
      refine Maximal.mma_done hA hmax (hs x hx) fun p hp => ?_
      obtain ⟨hx1, hx2, -, -⟩ := hx
      obtain ⟨hp1, hp2, -, ⟨d, si, ai, mask, -, -, -, -, hpi, -⟩, -⟩ :=
        TcMma.completionPrecedes_iff.mp hp
      exact ih p (by omega) ⟨hp1.trans hx1, hp2.trans hx2, Or.inl ⟨d, si, ai, mask, hpi⟩, s, hi⟩
  intro x hx
  exact key (x.2 + 1) x (by omega) hx

/-- A maximal execution has delivered every commit's notification to every target rank, provided
each operation the commit tracks has its operand snapshot. The snapshot is the only premise; the
completion of earlier operations is derived. -/
theorem Maximal.commit_notified_of_started (hA : Assumption.WfFree L mem0 A)
    (hmax : Maximal L K A mem0 X) {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some m)
    (hs : ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaStarted x = true) :
    rank ∈ X.tcNotified i :=
  Maximal.commit_notified hA hmax hi ht (Maximal.tracked_mma_done hA hmax hi hs)

end

end PTX

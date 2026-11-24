-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Drain
public import Lemmas.Step.WfInOrder

@[expose] public section

/-! # Drained stages under assumptions that keep commit arrive-ons in order

The drain lemmas of `Lemmas/Step/Drain.lean` for kernels whose assumptions constrain executions,
when the constraints survive every extension that performs its commit arrive-ons in order
and add no read (`Assumption.WfStep sel`); assumptions without a constraint qualify
(`WfFree.step`).

* The completion of a CLC request (`Maximal.clc_notified_inOrder`) and of an MMA
  (`Maximal.mma_done_inOrder`, `Maximal.tracked_mma_done_inOrder`) performs no commit arrive-on.
* A commit's arrive-on at rank `r` is performed after the arrive-on at `r` of the previous commit
  of its thread, when that commit is at a site in `sel` (`tc_notify_counted_inOrder`). A maximal
  execution has performed every arrive-on whose tracked operations have their operand snapshots
  (`Maximal.commit_notified_inOrder`), by induction on the commit's position in its thread: the
  previous commit at a site in `sel` targets the rank too (`hprev`), tracks only operations the
  later commit tracks, and so has performed its arrive-on first. -/

namespace PTX

open AsyncCopy

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

/-- Assumptions without a constraint keep it under every extension. -/
theorem Assumption.WfFree.step (hA : Assumption.WfFree L mem0 A) :
    Assumption.WfStep sel L K mem0 A :=
  fun _ _ _ _ _ _ a ha => hA a ha _

/-- An extension of a consistent execution that performs no commit arrive-on and adds no read
keeps the constraints. -/
theorem Assumption.WfStep.quiet (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {Y : Execution} (hle : X.le Y)
    (h : Y.tcNotified = X.tcNotified) (hr : X.NoNewRead Y) : ∀ a ∈ A, a.wf L mem0 Y :=
  hA X Y hX hle (Execution.notifiedInOrder_of_eq h) hr

/-! ## Cluster launch control -/

theorem clc_resolve_counted_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {i : EvId} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) (hn : (X.clc i).resolved = none) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨hg, hidx⟩ := issuer_thread hX he
  cases hr : X.clcState.response (Clc.requestId i) with
  | none =>
    have hY := consistent_failClc hX ⟨pc, he⟩ hr (hA.quiet hX (failClc_le hr) rfl
        (Execution.noNewRead_of_tr rfl))
    have hres : (X.failClc i).clcState.response (Clc.requestId i) = some none :=
      Function.update_self _ _ _
    have hz := consistent_resolveClc_checked hY ⟨pc, he⟩ hn
      (show Clc.Result L i (X.failClc i).clcState (Clc.responseOf L i none) from ⟨none, hres, rfl⟩)
      (hA.quiet hY (resolveClc_le hn) rfl (Execution.noNewRead_of_tr rfl))
    refine ⟨_, hz, Execution.le_trans (failClc_le hr) (resolveClc_le hn), ?_⟩
    have hc := resolveClc_size (X := X.failClc i) (r := Clc.responseOf L i none) hg hidx hn
    have hs : (X.failClc i).size L = X.size L := rfl
    omega
  | some answer =>
    have hz := consistent_resolveClc_checked hX ⟨pc, he⟩ hn
      (show Clc.Result L i X.clcState (Clc.responseOf L i answer) from ⟨answer, hr, rfl⟩)
      (hA.quiet hX (resolveClc_le hn) rfl (Execution.noNewRead_of_tr rfl))
    refine ⟨_, hz, resolveClc_le hn, ?_⟩
    have hc := resolveClc_size (X := X) (r := Clc.responseOf L i answer) hg hidx hn
    omega

theorem clc_write_counted_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {i : EvId} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) {c : Nat} (hc : c ∈ targets) (hn : c ∉ (X.clc i).written) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  cases hr : (X.clc i).resolved with
  | none => exact clc_resolve_counted_inOrder hA hX hi hr
  | some response =>
    obtain ⟨pc, he⟩ := hi
    obtain ⟨hg, hidx⟩ := issuer_thread hX he
    have hz := consistent_writeClc_checked hX ⟨pc, he⟩ hr hc hn
      (hA.quiet hX (writeClc_le X i c) rfl (Execution.noNewRead_of_tr rfl))
    refine ⟨_, hz, writeClc_le X i c, ?_⟩
    have hcount := writeClc_size (X := X) hg hidx hn
    omega

theorem clc_notify_counted_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {i : EvId} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) {c : Nat} (hct : c ∈ targets)
    (hn : c ∉ (X.clc i).notified) :
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
      (hA.quiet hX notifyClcRecord_le rfl (Execution.noNewRead_of_tr rfl))
    have hcount := markClcNotify_size (X := X) (c := c) hg hidx hn
    have hsame : (X.notifyClcRecord i c mb record).size L = (X.markClcNotify i c).size L := rfl
    refine ⟨X.notifyClcRecord i c mb record, hz, notifyClcRecord_le, ?_⟩
    rw [hsame, hcount]
    omega
  · exact clc_write_counted_inOrder hA hX hi hct hw

/-- A maximal execution has notified every target of every cancellation request. -/
theorem Maximal.clc_notified_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) {i : EvId} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) : ∀ c ∈ targets, c ∈ (X.clc i).notified := by
  intro c hc
  by_contra hn
  exact (hmax.not_grows (clc_notify_counted_inOrder hA hmax.1 hi hc hn)).elim

/-! ## Tensor Core MMA -/

/-- A maximal execution has completed every started MMA whose completion is ready. -/
theorem Maximal.mma_done_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hm : Maximal L K A mem0 X) {i : EvId} (hs : X.async.mmaStarted i = true)
    (hready : TcMma.CompletionReady L X i) : X.async.mmaDone i = true := by
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
    have hc := consistent_completeMma hm.1 hs hn hready
      (hA.quiet hm.1 (X.le_completeMma i) rfl (Execution.noNewRead_of_tr rfl))
    have hle := hm.2 _ hc (X.le_completeMma i)
    have hlt := completeMma_size hv hg hlen hn
    omega

/-- In a maximal execution every operation a commit tracks has completed, provided each has its
operand snapshot (as `Maximal.tracked_mma_done`). -/
theorem Maximal.tracked_mma_done_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) {i : EvId} {s : TcCommit.Spec} (hi : X.Commit i s)
    (hs : ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaStarted x = true) :
    ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaDone x = true := by
  have key : ∀ n : Nat, ∀ x : EvId, x.2 < n → AsyncCopy.TracksMma X x i →
      X.async.mmaDone x = true := by
    intro n
    induction n with
    | zero => intro x hlt; exact absurd hlt (by omega)
    | succ n ih =>
      intro x hlt hx
      refine Maximal.mma_done_inOrder hA hmax (hs x hx) fun p hp => ?_
      obtain ⟨hx1, hx2, -, -⟩ := hx
      obtain ⟨hp1, hp2, -, ⟨d, si, ai, mask, -, -, -, -, hpi, -⟩, -⟩ :=
        TcMma.completionPrecedes_iff.mp hp
      exact ih p (by omega) ⟨hp1.trans hx1, hp2.trans hx2, Or.inl ⟨d, si, ai, mask, hpi⟩, s, hi⟩
  intro x hx
  exact key (x.2 + 1) x (by omega) hx

/-! ## Tensor Core commit -/

/-- A commit's arrive-on at a target rank that has not happened can be appended as a counted
consistent extension, once every operation the commit tracks has completed (`hd`) and the previous
commit of its thread, when at a site in `sel`, has performed its arrive-on at that rank
(`hprev`). -/
theorem tc_notify_counted_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some m) (hn : rank ∉ X.tcNotified i)
    (hd : ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaDone x = true)
    (hprev : ∀ (j pc : Nat) (sp : TcCommit.Spec), X.get (i.1, j) = some ⟨pc, .tc (.commit sp)⟩ →
      sel pc = true → j < i.2 → (∀ k, j < k → k < i.2 → ¬ ∃ s, X.Commit (i.1, k) s) →
      rank ∈ X.tcNotified (i.1, j)) :
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
  have hle := X.le_notifyTcRecord i rank m rec
  have hord : X.NotifiedInOrder sel (X.notifyTcRecord i rank m rec) := by
    intro e r hr hnr j pc sp he hsel hj hb
    have hei : e = i ∧ r = rank := by
      have hr' : r ∈ (if e = i then insert rank (X.tcNotified e) else X.tcNotified e) := hr
      split_ifs at hr' with hei
      · rcases Finset.mem_insert.mp hr' with h | h
        · exact ⟨hei, h⟩
        · exact absurd h hnr
      · exact absurd hr' hnr
    obtain ⟨rfl, rfl⟩ := hei
    exact hle.2.2.2.2.2.2.2.2.2.2.2.2 _ (hprev j pc sp he hsel hj hb)
  exact ⟨X.notifyTcRecord i rank m rec,
    consistent_notifyTcRecord hX hi ht hn hd hid ha hchecked (hA X _ hX hle hord
        (Execution.noNewRead_of_tr rfl)),
    hle, notifyTcRecord_size hg hidx hn⟩

/-- **A maximal execution has performed every commit's arrive-on at every target rank**, provided
each operation the commit tracks has its operand snapshot, and the previous commit of a thread,
when at a site in `sel`, targets every rank the later commit targets (`hprev`). -/
theorem Maximal.commit_notified_inOrder (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X)
    (hprev : ∀ (g j j' pc pc' : Nat) (sp sp' : TcCommit.Spec) (rank : Fin 16) (m : Loc),
      X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → sel pc = true →
      X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ → j < j' →
      TcCommit.target sp' rank = some m → ∃ m', TcCommit.target sp rank = some m')
    {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {mb : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some mb)
    (hs : ∀ x, AsyncCopy.TracksMma X x i → X.async.mmaStarted x = true) :
    rank ∈ X.tcNotified i := by
  obtain ⟨g, n⟩ := i
  induction n using Nat.strong_induction_on generalizing s mb with
  | _ n ih =>
    by_contra hn
    refine hmax.not_grows (tc_notify_counted_inOrder hA hmax.1 hi ht hn
      (Maximal.tracked_mma_done_inOrder hA hmax hi hs) ?_)
    intro j pc sp he hsel hj _
    obtain ⟨pci, hei⟩ := hi
    obtain ⟨m', ht'⟩ := hprev g j n pc pci sp s rank mb he hsel hei hj ht
    exact ih j hj (hi := ⟨pc, he⟩) (ht := ht') (hs := fun x hx =>
      hs x ⟨hx.1, Nat.lt_trans hx.2.1 hj, hx.2.2.1, s, pci, hei⟩)

end

end PTX

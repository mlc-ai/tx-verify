-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.DrainInOrder
public import Lemmas.Quiet.Base

@[expose] public section

/-! # Drained stages under quiet extensions

`Lemmas/Step/DrainInOrder.lean` under `Assumption.WfQuiet`: the MMA completions and the commit
arrive-ons. -/

namespace PTX
open AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

/-- A maximal execution has completed every started MMA whose completion is ready. -/
theorem Maximal.mma_done_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
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
      (hA.quiet hm.1 (X.le_completeMma i) rfl (Execution.quietExt_of_tr rfl))
    have hle := hm.2 _ hc (X.le_completeMma i)
    have hlt := completeMma_size hv hg hlen hn
    omega

/-- In a maximal execution every operation a commit tracks has completed, provided each has its
operand snapshot (as `Maximal.tracked_mma_done`). -/
theorem Maximal.tracked_mma_done_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
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
      refine Maximal.mma_done_inOrderQ hA hmax (hs x hx) fun p hp => ?_
      obtain ⟨hx1, hx2, -, -⟩ := hx
      obtain ⟨hp1, hp2, -, ⟨d, si, ai, mask, -, -, -, -, hpi, -⟩, -⟩ :=
        TcMma.completionPrecedes_iff.mp hp
      exact ih p (by omega) ⟨hp1.trans hx1, hp2.trans hx2, Or.inl ⟨d, si, ai, mask, hpi⟩, s, hi⟩
  intro x hx
  exact key (x.2 + 1) x (by omega) hx

/-- A commit's arrive-on at a target rank that has not happened can be appended as a counted
consistent extension, once every operation the commit tracks has completed (`hd`) and the previous
commit of its thread, when at a site in `sel`, has performed its arrive-on at that rank
(`hprev`). -/
theorem tc_notify_counted_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
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
        (Execution.quietExt_of_tr rfl)),
    hle, notifyTcRecord_size hg hidx hn⟩

/-- **A maximal execution has performed every commit's arrive-on at every target rank**, provided
each operation the commit tracks has its operand snapshot, and the previous commit of a thread,
when at a site in `sel`, targets every rank the later commit targets (`hprev`). -/
theorem Maximal.commit_notified_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
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
    refine hmax.not_grows (tc_notify_counted_inOrderQ hA hmax.1 hi ht hn
      (Maximal.tracked_mma_done_inOrderQ hA hmax hi hs) ?_)
    intro j pc sp he hsel hj _
    obtain ⟨pci, hei⟩ := hi
    obtain ⟨m', ht'⟩ := hprev g j n pc pci sp s rank mb he hsel hei hj ht
    exact ih j hj (hi := ⟨pc, he⟩) (ht := ht') (hs := fun x hx =>
      hs x ⟨hx.1, Nat.lt_trans hx.2.1 hj, hx.2.2.1, s, pci, hei⟩)

end

end PTX

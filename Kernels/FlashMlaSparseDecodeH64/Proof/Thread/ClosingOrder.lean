-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.Final

public section

/-! # Actual closing arrivals precede the final role states -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingOrder

open PTX PTX.Flow ScoreClosingGate

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A role at a return or the final Tensor Memory release is past its closing CTA arrival. -/
@[expose] def AfterClosing : Machine.ThreadD → Prop
  | .wg0 d => d.site = .exit
  | .mma d => d.site = .exit
  | .tma d => d.site = .exit
  | .idle s => s = .exit
  | .done => True
  | _ => False

private theorem idle_entry (hpre : Pre P L mem0) : Thread.startSite L g ≠ .exit := by
  have hBatch := Wg1Mma.geBatch_false hpre (Wg1Mma.batchOf_lt_of_pre hpre g)
  have hSame : Thread.geBatch L g = Wg1Mma.geBatch L g := rfl
  unfold Thread.startSite
  rw [hSame, hBatch]
  split_ifs <;> simp_all

private theorem mma_entry (hpre : Pre P L mem0) : Wg1Mma.startSite P L g ≠ .exit := by
  have hBatch := Wg1Mma.geBatch_false hpre (Wg1Mma.batchOf_lt_of_pre hpre g)
  unfold Wg1Mma.startSite
  rw [hBatch]
  split_ifs <;> simp_all

private theorem mma_exit_predecessor (hpre : Pre P L mem0)
    {q d : Wg1Mma.D} {e : Event} (hn : Wg1Mma.next P L g q e = some (some d))
    (hD : d.site = .exit) : q.site = .outBar := by
  cases hq : q.site
  case outBar => rfl
  all_goals simp only [Wg1Mma.next, hq] at hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals
    have he := congrArg Wg1Mma.D.site hn
    rw [hD] at he
    try (rw [hq] at he)
    try (simp only [Wg1Mma.afterTopk, Wg1Mma.nextSite] at he)
    try split_ifs at he
    all_goals first | exact (mma_entry hpre he).elim | cases he

/-- A reached MMA return state immediately follows that lane's closing arrival. -/
theorem mma_out_bar_before_exit_state {j : Nat} {d : Wg1Mma.D}
    (hpre : Pre P L mem0) (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads)
    (hj : j ≤ (X.tr g).length)
    (hState : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hExit : d.site = .exit) :
    ∃ i < j, ∃ e q, X.get (g, i) = some e ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧ q.site = .outBar := by
  cases j with
  | zero =>
    rw [Frame.stateAt_zero] at hState
    cases hState
  | succ i =>
    obtain ⟨before, hBefore⟩ := Frame.stateAt_live ht hg hState (Nat.le_succ i)
    have hei : i < (X.tr g).length := by omega
    have he : X.get (g, i) = some (X.tr g)[i] := List.getElem?_eq_getElem hei
    have hNext := (Frame.stateAt_succ (C := Machine.code P L) he).symm.trans hState
    rw [hBefore, Option.bind_some] at hNext
    change Machine.next P L g before (X.tr g)[i] = some (some (.mma d)) at hNext
    cases before
    case mma q =>
      simp only [Machine.next] at hNext
      split at hNext
      · rename_i p hp
        cases hNext
        exact ⟨i, by omega, _, q, he, hBefore, mma_exit_predecessor hpre hp hExit⟩
      · split at hNext <;> cases hNext
      · split at hNext <;> cases hNext
    case prologue s =>
      simp only [Machine.next] at hNext
      split at hNext
      · cases hNext
      · split at hNext
        · rename_i w _
          split_ifs at hNext
          · fin_cases w <;> cases hNext
          · cases hNext
        · cases hNext
      · cases hNext
    case head =>
      cases hk : ((X.tr g)[i]).kind <;> simp only [Machine.next, hk, reduceCtorEq] at hNext
      simp only [Machine.headStart] at hNext
      split_ifs at hNext <;> cases hNext
      cases hExit
    all_goals simp only [Machine.next] at hNext
    all_goals repeat' split at hNext
    all_goals cases hNext

private theorem tma_exit_predecessor
    {q d : Wg1Tma.D} {e : Event} (hn : Wg1Tma.next P L g q e = some (some d))
    (hD : d.site = .exit) : q.site = .barrier := by
  cases hq : q.site
  case barrier => rfl
  all_goals simp only [Wg1Tma.next, hq] at hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals
    have he := congrArg Wg1Tma.D.site hn
    rw [hD] at he
    try (rw [hq] at he)
    try simp only [Wg1Tma.firstLenSite, Wg1Tma.beginLoop, Wg1Tma.afterFree,
      Wg1Tma.afterIssue, Wg1Tma.afterCoord] at he
    try split_ifs at he
    all_goals cases he

private theorem idle_exit_predecessor {q d : Thread.Site} {e : Event}
    (hn : Thread.next L q e = some (some d)) (hD : d = .exit) : q = .sync := by
  subst d
  cases q <;> simp only [Thread.next] at hn
  case sync => rfl
  all_goals repeat' split at hn
  all_goals cases hn

set_option maxHeartbeats 900000 in
private theorem after_step {d q : Machine.ThreadD} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e o)
    (ht : Machine.next P L g d e = some (some q)) (hClose : AfterClosing q) :
    AfterClosing d ∨ e.kind = .bar 12 none .sync := by
  cases d
  case wg0 d =>
    have hNext := ht
    simp only [Machine.next] at ht
    split at ht
    · rename_i d' hs
      cases ht
      have hEq : d'.site = .exit := hClose
      obtain ⟨s, hD, hSite⟩ := ScoreReleaseTrace.exit_predecessor hNext hEq
      have hd := Machine.ThreadD.wg0.inj hD
      exact .inr (closing_kind hpre hf (hd.symm ▸ hSite))
    · split at ht
      · rename_i h
        rcases h with h | h
        · exact .inl h
        · exact .inr (closing_kind hpre hf h)
      · cases ht
    · cases ht
  case mma d =>
    simp only [Machine.next] at ht
    split at ht
    · rename_i d' hs
      cases ht
      exact .inr (closing_kind hpre hf (mma_exit_predecessor hpre hs hClose))
    · split at ht
      · cases ht
        exact (idle_entry hpre hClose).elim
      · cases ht
    · split at ht
      · rename_i hd
        exact .inl hd
      · cases ht
  case tma d =>
    simp only [Machine.next] at ht
    split at ht
    · rename_i d' hs
      cases ht
      exact .inr (closing_kind hpre hf (tma_exit_predecessor hs hClose))
    · split at ht
      · rename_i hd
        exact .inl hd
      · split at ht
        · cases ht
          exact (idle_entry hpre hClose).elim
        · cases ht
    · split at ht
      · rename_i hd
        exact .inl hd
      · cases ht
  case idle s =>
    simp only [Machine.next] at ht
    split at ht
    · rename_i s' hs
      cases ht
      exact .inr (closing_kind hpre hf (idle_exit_predecessor hs hClose))
    · cases ht
    · split at ht
      · rename_i hd
        exact .inl hd
      · cases ht
  case index d =>
    simp only [Machine.next] at ht
    split at ht
    · cases ht; exact hClose.elim
    · split at ht
      · rename_i hd
        exact .inr (closing_kind hpre hf hd)
      · cases ht
    · cases ht
  case wg2 d =>
    simp only [Machine.next] at ht
    split at ht
    · cases ht; exact hClose.elim
    · split at ht
      · rename_i hd
        exact .inr (closing_kind hpre hf hd)
      · cases ht
    · cases ht
  case prologue s =>
    simp only [Machine.next] at ht
    split at ht
    · cases ht; exact hClose.elim
    · split at ht
      · rename_i w _
        split_ifs at ht
        · fin_cases w <;> cases ht
          · change Wg0.firstSite P = .exit at hClose
            simp only [Wg0.firstSite, Wg0.afterSink, Wg0.afterLen] at hClose
            split_ifs at hClose
          · exact hClose.elim
          · exact hClose.elim
        · cases ht
      · cases ht
    · cases ht
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at ht
    simp only [Machine.headStart] at ht
    split_ifs at ht <;> cases ht
    all_goals first | exact hClose.elim | cases hClose | exact (idle_entry hpre hClose).elim
  case done => cases ht

private def arrived (events : List Event) : Prop :=
  ∃ e ∈ events, e.kind = .bar 12 none .sync

private def state_has_arrival (d : Option Machine.ThreadD) (events : List Event) : Prop :=
  ∀ q, d = some q → AfterClosing q → arrived events

private theorem arrived_step {d q : Option Machine.ThreadD} {es : List Event} {e : Event}
    {o : Option TState} (hpre : Pre P L mem0) (h : state_has_arrival d es)
    (hf : (Machine.machine P L g).Fired d e o)
    (hn : (Machine.machine P L g).next d e = some q) :
    state_has_arrival q (es ++ [e]) := by
  intro d' hQ hAfter
  subst q
  cases d with
  | none => cases hn
  | some d =>
    rcases after_step hpre hf hn hAfter with hOld | hClose
    · obtain ⟨f, hf', hkind⟩ := h d rfl hOld
      exact ⟨f, List.mem_append_left _ hf', hkind⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), hClose⟩

/-- A followed state past the CTA closing gate has the actual arrival in its trace prefix. -/
theorem arrival_before_state (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    {i : Nat} {d : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hAfter : AfterClosing d) :
    ∃ j < i, ∃ tag, X.get (g, j) = some ⟨tag, .bar 12 none .sync⟩ := by
  have ha := (hs.produces (hX.thr g hg)).prefix_induction state_has_arrival
    (by intro q hq h; cases hq; exact h.elim)
    (fun _ _ _ _ _ => arrived_step hpre) i (some d) hd
  obtain ⟨⟨tag, kind⟩, he, hk⟩ := ha d rfl hAfter
  change kind = _ at hk
  subst kind
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  have hLen := (List.getElem?_eq_some_iff.mp hj).1
  have hLT : j < i := hLen.trans_le (List.length_take_le _ _)
  exact ⟨j, hLT, tag, (List.getElem?_take_of_lt hLT).symm.trans hj⟩

private def return_op : Op → Bool
  | .ret | .exit => true
  | _ => false

set_option maxRecDepth 100000 in
private theorem return_locations : OpPcsFast kernel.code return_op [3611] = true := by
  decide +kernel

local macro "return_location" : tactic => `(tactic|
  (first
   | decide +kernel
   | (rename_i a; revert a; decide +kernel)
   | (rename_i a b; revert a b; decide +kernel)
   | (rename_i a b c; revert a b c; decide +kernel)))

private theorem after_of_return_tag {d : Machine.ThreadD}
    (hp : (Machine.code P L g).pc d = 3611) : AfterClosing d := by
  cases d
  case prologue s =>
    change s.pc = 3611 at hp
    exfalso
    cases s <;> revert hp <;> return_location
  case wg0 d =>
    change d.site.pc = 3611 at hp
    change d.site = .exit
    generalize h : d.site = s at hp ⊢
    clear d h
    cases s <;> revert hp <;> return_location
  case mma d =>
    change d.site.pc = 3611 at hp
    change d.site = .exit
    generalize h : d.site = s at hp ⊢
    clear d h
    cases s <;> revert hp <;> return_location
  case tma d =>
    change d.site.pc = 3611 at hp
    change d.site = .exit
    generalize h : d.site = s at hp ⊢
    clear d h
    cases s <;> revert hp <;> return_location
  case index d =>
    change d.site.pc = 3611 at hp
    change False
    generalize h : d.site = s at hp
    clear d h
    cases s <;> revert hp <;> return_location
  case idle s =>
    change s.pc = 3611 at hp
    change s = .exit
    cases s <;> revert hp <;> return_location
  case wg2 d =>
    change d.site.pc = 3611 at hp
    change False
    generalize h : d.site = s at hp
    clear d h
    cases s <;> revert hp <;> return_location
  case head => cases hp
  case done => trivial

/-- The actual return of a followed thread comes from its closing role state. -/
theorem return_state
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {i tag : Nat} (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧ AfterClosing d := by
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨_, ins, _, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
  have ho : return_op ins.op = true := by
    rcases fires_exit_op hf rfl with ho | ho <;> rw [ho] <;> rfl
  exact ⟨d, hd, after_of_return_tag (List.mem_singleton.mp (OpPcsFast.mem return_locations hc ho))⟩

/-- Every actual return in a followed trace has executed its CTA closing arrival. -/
theorem arrival_before_exit (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {i tag : Nat} (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    ∃ j < i, ∃ tag, X.get (g, j) = some ⟨tag, .bar 12 none .sync⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hd, hAfter⟩ := return_state hX hs ht he
  exact arrival_before_state hpre hX (hs g hg).machine hg hd hAfter

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingOrder

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The row total stays live throughout the output epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RowTotalHistory

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The final row total, reference and peak survive each output step. -/
def Retained (old d : D) : Prop :=
  old.site.needsRowTotal = true ∧ d.li = old.li ∧ reference d = reference old ∧
    d.peak = old.peak ∧ d.block = old.block

set_option maxHeartbeats 3500000 in
private theorem role_step {g : Nat} {old d : D} {e : Event}
    (hn : Wg0.next P L g old e = some (some d)) (hRow : d.site.needsRowTotal = true) :
    (old.site = .lseRead ∧ ∃ a values, e.kind = .rd a values) ∨ Retained old d := by
  cases hd : old.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hm
        cases hRow
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hm
      cases hRow
    · cases hn
  case lseRead =>
    split at hn
    · rename_i a values hKind
      exact .inl ⟨rfl, a, values, hKind⟩
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [Retained, hd, reference, afterSink, afterLen, afterScoreSite, epiAfterBar,
      loadOutput, loadScores, Site.needsRowTotal] at hRow ⊢
  all_goals (try split_ifs at hRow ⊢) <;> simp_all

private theorem init_precedes_total {g : Nat} : (Wg0.init P L g).site.needsRowTotal = false := by
  simp only [Wg0.init, firstSite, afterSink, afterLen]
  split_ifs <;> rfl

private theorem composed_step {g : Nat} {q : Machine.ThreadD} {d : D} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) (hRow : d.site.needsRowTotal = true) :
    ∃ old, q = .wg0 old ∧
      ((old.site = .lseRead ∧ ∃ a values, e.kind = .rd a values) ∨ Retained old d) := by
  cases q
  case wg0 old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i a hNext
      cases hn
      exact ⟨old, rfl, role_step hNext hRow⟩
    · split at hn <;> cases hn
    · cases hn
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          rw [init_precedes_total] at hRow
          cases hRow
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
  all_goals cases hn

/-- A final epilogue state preserves the numerical row fields of its actual LSE read successor. -/
theorem source {g i : Nat} {d : D}
    (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hRow : d.site.needsRowTotal = true) :
    ∃ j old mid e a values, j < i ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 old)) ∧
      old.site = .lseRead ∧ X.get (g, j) = some e ∧ e.kind = .rd a values ∧
      X.Reads (g, j) a values ∧ Machine.next P L g (.wg0 old) e = some (some (.wg0 mid)) ∧
      d.li = mid.li ∧ reference d = reference mid ∧ d.peak = mid.peak ∧ d.block = mid.block := by
  induction i generalizing d with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i ih =>
    have hi' : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨q, hq⟩ := Frame.stateAt_live ht hg hd (Nat.le_succ i)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hq] at hn
    obtain ⟨old, rfl, hRead | hKeep⟩ := composed_step hn.symm hRow
    · obtain ⟨hSite, a, values, hk⟩ := hRead
      have hr : X.Reads (g, i) a values := ⟨e.pc, he.trans (by cases e; cases hk; rfl)⟩
      exact ⟨i, old, d, e, a, values, Nat.lt_succ_self _, hq, hSite, he, hk, hr, hn.symm,
        rfl, rfl, rfl, rfl⟩
    · obtain ⟨j, before, mid, first, a, values, hj, hBefore, hSite, hGet, hKind, hRead, hNext,
        hL, hR, hP, hB⟩ := ih hi'.le hq hKeep.1
      exact ⟨j, before, mid, first, a, values, hj.trans (Nat.lt_succ_self _), hBefore, hSite,
        hGet, hKind, hRead, hNext, hKeep.2.1.trans hL, hKeep.2.2.1.trans hR,
        hKeep.2.2.2.1.trans hP, hKeep.2.2.2.2.trans hB⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RowTotalHistory

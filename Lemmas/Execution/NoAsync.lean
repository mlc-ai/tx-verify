-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.NoTma
public import Lemmas.Clc.ClcExecution

@[expose] public section

/-! Consequences of the absence of independent effects. These are derived simplifications
for kernels without async instructions, not restrictions on Core executions. -/
namespace PTX
noncomputable section
namespace Execution.NoTma
variable {X : Execution} (h : EmptyAsync X)
include h

/-- An empty-effect execution has the default asynchronous snapshot. -/
theorem snapshot_eq_empty : X.async = ({} : AsyncCopy.Snapshot) := by
  cases hs : X.async with
  | mk c op d arr =>
    have hc : c = fun _ => ({} : AsyncCopy.Effects) := funext fun i => by
      have hi := (h.1 i).1
      simpa only [hs] using hi
    have ho : op = fun _ => none := funext fun i => by
      have hi := (h.1 i).2.1
      simp only [hs, AsyncCopy.Snapshot.mmaStarted] at hi
      cases he : op i with
      | none => rfl
      | some values => simp [he] at hi
    have hd : d = fun _ => false := funext fun i => by
      have hi := (h.1 i).2.2.1
      simpa only [hs] using hi
    have ha : arr = fun _ => false := funext fun i => by
      have hi := (h.1 i).2.2.2
      simpa only [hs] using hi
    subst c op d arr
    rfl

theorem not_asyncPresent (i : EvId) (p : AsyncCopy.Part) : ¬ X.AsyncPresent i p := by
  obtain ⟨hc, -, hd, ha⟩ := h.1 i
  obtain ⟨htn, hst, hcl, hmul⟩ := h.2.2 i
  cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, snapshot_eq_empty h, htn, hst, hcl,
    hmul]

theorem not_asyncRead (i : EvId) (p : AsyncCopy.Part) (a : Acc)
    (bs : List (Option Byte)) : ¬ X.MemReads (.async i p) a bs := by
  obtain ⟨hc, hs, _⟩ := h.1 i
  obtain ⟨htn, hst, hcl, hmul⟩ := h.2.2 i
  cases p <;> simp [Execution.MemReads, Execution.MmaRead, snapshot_eq_empty h, htn, hst]

theorem not_asyncWrite (i : EvId) (p : AsyncCopy.Part) (a : Acc)
    (bs : List Byte) : ¬ X.MemWrites (.async i p) a bs := by
  obtain ⟨hc, _, _⟩ := h.1 i
  obtain ⟨htn, hst, hcl, hmul⟩ := h.2.2 i
  cases p <;> simp [Execution.MemWrites, Clc.ResponseWrite, hc, htn, hst, hcl]

/-- An empty-effect execution reads only through thread accesses: a plain read or the read of an
atomic read-modify-write. -/
theorem memReads_thread {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)}
    (he : X.MemReads e a bs) :
    ∃ i, e = .thread i ∧ (X.Reads i a bs ∨ ∃ new, X.Rmw i a bs new) := by
  cases e with
  | thread i => exact ⟨i, rfl, he⟩
  | async i p => exact False.elim (not_asyncRead h i p a bs he)

/-- An empty-effect execution writes only through thread accesses: a plain write or the write of an
atomic read-modify-write. -/
theorem memWrites_thread {e : AsyncCopy.Ref} {a : Acc} {bs : List Byte}
    (he : X.MemWrites e a bs) :
    ∃ i, e = .thread i ∧ (X.Writes i a bs ∨ ∃ old, X.Rmw i a old (some bs)) := by
  cases e with
  | thread i => exact ⟨i, rfl, he⟩
  | async i p => exact False.elim (not_asyncWrite h i p a bs he)

theorem no_object_before (e f : AsyncCopy.Ref) (m : Loc) :
    ¬ MBarrier.Before (X.objects m) e f := by
  simp [h.2.1 m, MBarrier.Before]

omit h

/-- Pending footprints also disappear when their issuing instruction is absent. -/
theorem intent_thread (hn : X.NoTma) {e : AsyncCopy.Ref} {a : Acc} {w : Bool}
    (he : X.Intent e a w) : ∃ i, e = .thread i ∧ X.Access i a w := by
  cases e with
  | thread i => exact ⟨i, rfl, he⟩
  | async i p =>
    exfalso
    cases p <;>
      simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
        and_false] at he
    all_goals first
      | (rcases he.2 with ⟨_, ⟨pc, hi⟩, _⟩ | hb
         · cases hn _ _ _ hi
         · obtain ⟨pc, hi⟩ := hb; cases hn _ _ _ hi)
      | (obtain ⟨_, ⟨pc, hi⟩, _⟩ := he.2; cases hn _ _ _ hi)
      | (obtain ⟨_, ⟨pc, hi⟩, _, _⟩ := he.2; cases hn _ _ _ hi)
      | (obtain ⟨_, _, ⟨pc, hi⟩, _⟩ := he.2; cases hn _ _ _ hi)
      | (obtain ⟨_, _, ⟨pc, hi⟩, _, _⟩ := he.2; cases hn _ _ _ hi)
      | (obtain ⟨-, -, hm⟩ := he
         rcases hm with ⟨_, _, _, _, hi, -⟩ | ⟨_, _, _, hi, -, -⟩
         · exact (hn.noTc.not_mma_issue hi).elim
         · obtain ⟨pc, hpc⟩ := hi; cases hn _ _ _ hpc)

theorem memTouches_thread (hn : X.NoTma) {e : AsyncCopy.Ref} {a : Acc}
    (he : X.MemTouches e a) : ∃ i, e = .thread i ∧
      ((∃ bs, X.Reads i a bs) ∨ (∃ bs, X.NcReads i a bs) ∨ (∃ bs, X.Writes i a bs) ∨
        ∃ old new, X.Rmw i a old new) := by
  rcases he with ⟨w, hw⟩ | ⟨i, bs, hi, hr⟩
  · obtain ⟨i, rfl, hi⟩ := intent_thread hn hw
    refine ⟨i, rfl, ?_⟩
    rcases hi with ⟨bs, hr, _⟩ | ⟨bs, hw, _⟩ | ⟨old, new, hrmw⟩
    · exact .inl ⟨bs, hr⟩
    · exact .inr (.inr (.inl ⟨bs, hw⟩))
    · exact .inr (.inr (.inr ⟨old, new, hrmw⟩))
  · exact ⟨i, hi, .inr (.inl ⟨bs, hr⟩)⟩

/-- With no async instructions, the drain obligation is vacuous, as a theorem. -/
theorem drained (hn : X.NoTma) : AsyncDrained X := by
  intro i p hp
  obtain ⟨s, m, hc, -, -⟩ | ⟨s, hc, -, -⟩ | ⟨m, noinc, ha, -⟩ | ⟨ht, -⟩ |
    ⟨s, t, c, hcl, -, -⟩ | ⟨a, s, ht, -⟩ | ⟨a, s, ht, -⟩ | ⟨s, r, m, hc, ht, -⟩ := hp
  · exact (hn.not_copy hc).elim
  · exact (hn.not_copy hc).elim
  · obtain ⟨pc, hpc⟩ := ha; cases hn _ _ _ hpc
  · rcases ht with hm | ⟨_, hcp⟩ | ⟨_, hsh⟩
    · obtain ⟨_, _, _, _, hm⟩ := hm; exact (hn.noTc.not_mma_issue hm).elim
    · obtain ⟨pc, hpc⟩ := hcp; cases hn _ _ _ hpc
    · obtain ⟨pc, hpc⟩ := hsh; cases hn _ _ _ hpc
  · obtain ⟨pc, hpc⟩ := hcl; cases hn _ _ _ hpc
  · obtain ⟨pc, hpc⟩ := ht; cases hn _ _ _ hpc
  · obtain ⟨pc, hpc⟩ := ht; cases hn _ _ _ hpc
  · exact (hn.noTc.not_commit hc).elim

theorem pair_drained (hn : X.NoTma) (L : Launch) : Tmem.Pair.Drained L X := by
  intro i pc group dst action hi
  cases hn _ _ _ hi

theorem complete_of_exits (hn : X.NoTma) (L : Launch)
    (hx : ∀ g < L.threads, ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) : Complete L X :=
  ⟨fun g hg => Or.inr (hx g hg), hn.drained, hn.pair_drained L⟩

theorem complete_iff (hn : X.NoTma) (L : Launch) (hc : ClcOk L X) :
    Complete L X ↔ ∀ g < L.threads, ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩ := by
  constructor
  · intro hd g hg
    rcases hd.1 g hg with ⟨_, req, ho⟩ | hx
    · obtain ⟨i, s, targets, _, ⟨pc, hi⟩, _⟩ := hc.canceled_has_issue ho
      cases hn _ _ _ hi
    · exact hx
  · exact hn.complete_of_exits L

end Execution.NoTma
end
end PTX

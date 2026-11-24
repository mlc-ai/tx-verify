-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.NoBarArrive
public import Kernels.TmaCopy.Proof.MemoryFacts
public import Lemmas.Kernel.Next
public import Lemmas.Step.BulkDrain
public import Lemmas.Step.ReadSource
public import Lemmas.Flow.SpinsAtLoop
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Every maximal execution is complete

The open obligations of an execution are its pending threads and its bulk copy
(`Execution.MbarBulk.open_cases`). A maximal execution has completed the copy, whose source no write
covers (`Maximal.bulk_notified`). A pending thread is released (no barriers), and steps by its next
event (`thread_steps`): the undefined behaviour after its machine stopped, the initialization and
the arrival with their checked records, the fence, the copy issue, the read of `buf`, the write of
`B` and the exit, each a counted extension of the safe execution. At the poll, a ready barrier is
polled successfully; otherwise the barrier's phase is even, so the copy has not completed
(`final_state`), and after a failed poll the copy is an open obligation of smaller rank (`oblRank`).
Synchronization is guarded (`syncGuarded`): the poll heads a spinning loop, no write releases and no
record faults. -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

/-- The rank of an obligation: a thread above the copy its poll waits for. -/
def oblRank (_ : Execution) : Descent.Obligation → Nat
  | .thread _ => 1
  | _ => 0

/-- The kernel has no assumptions. -/
theorem wfFree {L : Launch} {mem0 : Mem0} : Assumption.WfFree L mem0 ([] : List Assumption) :=
  fun _ ha => by cases ha

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {X : Execution}

section
variable (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)
include ht hX

/-- No write releases. -/
theorem no_release {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get e = some ⟨pc, .wr a bs⟩) : a.release = false := by
  rw [(writes_cases ht hX ⟨pc, he⟩).2.1]

/-- **Synchronization is guarded**: the poll is the canonical spin (`spin`), no write releases,
the kernel has no thread fence and no record faults. -/
theorem syncGuarded : SyncGuarded L kernel X :=
  ⟨fun _ _ _ _ _ _ he => by rw [wait_pc ht hX he]; exact spin,
    fun e f => ⟨(fun ⟨a, b, bs, cs, hw, _, hrel, _⟩ => by
        rcases memWrites_cases ht hX hw with ⟨i, -, rfl, -⟩ | ⟨h, -⟩
        · cases hrel
        · cases h),
      not_fenceSync_of_noFence (fun _ _ _ h => no_threadFence ht hX h) e f⟩,
    fun _ _ _ _ _ hr _ _ _ => object_fault_free ht hX (List.mem_of_getElem? hr)⟩

/-- No event is a CTA barrier operation or a group wait. -/
theorem no_blocking {v : EvId} {pc : Nat} {k : Kind} (hp : X.get v = some ⟨pc, k⟩)
    (hk : (∃ id count mode, k = .bar id count mode) ∨ (∃ mode n, k = .bulkWait mode n) ∨
      ∃ n, k = .asyncWait n) : False := by
  rcases (event_cases ht hX hp).2 with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
    ⟨-, -, he⟩ | ⟨-, -, -, ⟨ok, he⟩ | ⟨i, -, -, -, hc⟩⟩
  all_goals try (rcases hk with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [exE, initE, fenceE, arriveE, bulkE, waitE] at he)
  rcases hc with ⟨bs', he⟩ | ⟨_, _, _, _, _, he⟩ | he | ⟨_, _, he, -⟩ <;>
    rcases hk with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [rdE, wrE, exE] at he

/-- **Every thread is released**: no event is a CTA barrier operation or a group wait. -/
theorem released (g : Nat) : Step.Released L X g :=
  (mbarBulk ht hX).released
    (fun _ _ _ _ h => (no_blocking ht hX h (.inl ⟨_, _, _, rfl⟩)).elim)
    (fun _ _ h hk => (no_blocking ht hX h (.inr hk)).elim)

/-- Every thread may perform its first event. -/
theorem launched (g : Nat) : Step.Launched L X g :=
  fun ⟨_, _, _, hi⟩ => (no_clc ht hX hi).elim

/-- The copy completions keep the Tensor Core read obligation: the kernel has no `tcgen05`
instruction. -/
theorem copyReadOk : CopyReadOk L [] mem0 X :=
  copyReadOk_of_noTcRead (fun _ _ _ _ _ ⟨_, hi⟩ => noTc ht hX _ _ _ hi)
    (fun _ _ _ _ ⟨_, hi⟩ => noTc ht hX _ _ _ hi) (fun _ _ ⟨_, hi⟩ => noTc ht hX _ _ _ hi)
    (fun _ _ ⟨_, hi⟩ => noTc ht hX _ _ _ hi)

end

variable (hpre : Pre L A B x mem0) (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)

include hpre ht hX in
/-- The copy writes `buf` whole from the 16 allocated bytes at `A`, which no write covers. -/
theorem bulkSources : BulkSources mem0 X := by
  intro i s m hb _
  obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
  refine ⟨rfl, rfl, rfl, fun k hk => ⟨?_, fun w a bs hw => no_write_input hpre ht hX hw hk⟩⟩
  simpa [copySpec, bulkSpec, gA, Loc.at] using hpre.inputAlloc k hk

include hpre ht in
/-- **A pending thread of a maximal execution steps.** -/
theorem thread_steps (hsafe : ¬ Unsafe L kernel [] mem0 X) (hmax : Maximal L kernel [] mem0 X)
    {g : Nat} (hp : Frame.Pending L X g) :
    Descent.Steps L kernel [] mem0 (Descent.Obl L) oblRank X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub := no_local_ub hpre ht hX
  have hst := (conflicts_ordered hpre ht hX).strongOrdered
  have hsg := syncGuarded ht hX
  have hrel : Step.Released L X g := released ht hX g
  have hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false :=
    fun _ _ _ _ he => no_release ht hX he
  have hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false :=
    fun _ _ _ _ _ he => (no_rmw ht hX he).elim
  have hnf : ∀ e sem s, ¬ X.ThreadFence e sem s := fun _ _ _ => no_threadFence ht hX
  cases hσ : stateAt L A B X g (X.tr g).length with
  | none => exact Descent.dead_steps wfFree hmax hub ht.sound hp hσ hrel
  | some σ =>
    cases σ with
    | none => exact absurd hσ (ht.tracked g _ hg)
    | some s =>
      obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
      obtain ⟨t1, m, hl, hpc, hout, hm⟩ := ht.fire hg hσ hrun
      have hJ := ht.along hg le_rfl hσ
      rw [List.take_length] at hJ
      have hne : ∀ e es, X.tr g = e :: es → X.tr g ≠ [] := fun _ _ h h' => by rw [h] at h'; cases h'
      cases s with
      | init =>
        obtain ⟨u, rfl⟩ := hm
        refine Descent.object_steps wfFree hX hsafe hst hsg hnr hnrmw hnf hg
          (.inr (launched ht hX g)) hrel hrun hl hout (k := .mbInit (mbar L.sharedBase) 1)
          ⟨rfl, rfl⟩
          (.inr ⟨_, _, rfl⟩) (mb := mbar L.sharedBase) (act := .init 1) (fun _ _ h => by cases h)
          fun l' => ?_
        by_cases h : l' = mbar L.sharedBase
        · subst h
          simp [objectAction, snoc_get_new]
        · simp [objectAction, snoc_get_new, h, Ne.symm h]
      | fence =>
        obtain ⟨u, rfl⟩ := hm
        exact Descent.quiet_steps wfFree hX hsafe hst hsg hnr hnrmw hnf hg
          (.inl (hne _ _ hJ.2)) hrel hrun hl hout ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
      | arrive =>
        obtain ⟨u, rfl⟩ := hm
        refine Descent.object_steps wfFree hX hsafe hst hsg hnr hnrmw hnf hg (.inl (hne _ _ hJ.2))
          hrel hrun hl hout (k := .arrive (mbar L.sharedBase) 16) ⟨rfl, rfl⟩
          (.inl ⟨_, _, _, _, _, rfl⟩) (mb := mbar L.sharedBase) (act := .arrive 1 16)
          (fun _ _ h => by cases h) fun l' => ?_
        by_cases h : l' = mbar L.sharedBase
        · subst h
          simp [objectAction, snoc_get_new]
        · simp [objectAction, snoc_get_new, h, Ne.symm h]
      | bulk =>
        obtain ⟨u, rfl⟩ := hm
        exact .inl (Step.issue_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
          hst hg (hne _ _ hJ.2) hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩
          (.inr (.inr ⟨_, rfl⟩)) (fun _ ha => by cases ha)
          (hsg.snoc hnr hnrmw hnf (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
            (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))
      | wait =>
        obtain ⟨h0, n, htr⟩ := hJ
        subst h0
        have hne' : X.tr 0 ≠ [] := hne _ _ (by rw [htr]; rfl)
        have h3 : X.get (0, 3) = some (bulkE A L.sharedBase) := by
          change (X.tr 0)[3]? = _
          rw [htr, issue_get (by decide)]
          rfl
        obtain ⟨before, hstate, hphase⟩ := final_state ht hX h3 (by decide)
        refine Descent.mbar_wait_steps wfFree hub hmax hp hrel hne' (m := mbar L.sharedBase)
          (pcw := Flow.mbarWait_0) (par := 0) (Q := fun _ => True) (fun t' hrun' ok => ?_) hstate
          fun sc _ hph _ => ⟨.bulk, fun hall => ?_, by simp [oblRank]⟩
        · obtain ⟨t1', m', hl', hpc', hout', k', rfl⟩ := ht.fire hg hσ hrun'
          exact ⟨t1', k' ok, .cta, hl', ⟨_, hout', ok, by rw [hpc']; rfl, rfl⟩, fun _ => trivial⟩
        · have hbY : (Step.failedPoll X 0 Flow.mbarWait_0 0 (mbar L.sharedBase) true sc before).Copy
              (0, 3) (copySpec A L.sharedBase) :=
            ⟨_, Execution.le_get (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) h3⟩
          have hn : (X.async.copies (0, 3)).notified = true := hall _ _ hbY
          rw [hphase hn] at hph
          cases hph
      | load =>
        obtain ⟨k, rfl⟩ := hm
        obtain ⟨-, n, htr⟩ := hJ
        exact .inl (Step.read_source_counted_extension hX hg (hne _ _ (by rw [htr]; rfl)) hrel
          hrun hl hout (fun _ _ _ _ ha => by cases ha) hsg)
      | store v =>
        obtain ⟨-, n, bs, htr, -⟩ := hJ
        have hne' := hne _ _ (by rw [htr]; rfl)
        rcases hm with ⟨hv, u, rfl⟩ | ⟨hv, f, rfl⟩
        · exact .inl (Step.plain_counted_extension hX hg (.inl hne') hrel hrun hl (o := some u)
            (e := ⟨t1.pc, .wr { loc := gB B, size := 4 } v.toBytes⟩) ⟨_, hout, rfl, rfl⟩ rfl
            rfl (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun _ _ _ h => by cases h) rfl
            (hX.tmemPairResult.snoc_last fun _ _ _ _ hget => (noTc ht hX _ _ _ hget).elim)
            (fun _ ha => by cases ha))
        · exact Descent.ub_steps wfFree hX hg hne' hrel hrun hl hout
      | exit =>
        subst hm
        exact .inl (Step.plain_counted_extension hX hg (.inr (launched ht hX g)) hrel hrun hl
          (o := none) (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
          (hX.tmemPairResult.snoc_not_wr nofun) (fun _ ha => by cases ha))

omit ht hX in
include hpre in
/-- **Every maximal execution is complete.** -/
theorem progress_goal (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A B X)
    (hS : SafeGoal kernel [] L mem0) : ProgressGoal kernel [] L mem0 :=
  Descent.progress_of_steps (Descent.Obl L) oblRank
    (fun _ _ hn => Descent.cover hn)
    fun X o hmax ho => by
      have ht := hT X hmax.1
      rcases (mbarBulk ht hmax.1).open_cases ho with ⟨g, rfl⟩ | rfl
      · exact thread_steps hpre ht (hS.2 X hmax.1) hmax ho
      · refine (ho fun i s hb => ?_).elim
        obtain ⟨-, rfl⟩ := bulk_cases ht hmax.1 hb
        exact Maximal.bulk_notified wfFree hmax (bulkSources hpre ht hmax.1) (copyReadOk ht hmax.1)
          hb rfl

end

end PTX.Kernels.TmaCopy.Proof

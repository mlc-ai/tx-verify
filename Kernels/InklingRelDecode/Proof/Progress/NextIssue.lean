-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Next
public import Lemmas.Step.TcLoad

@[expose] public section

/-!
# Progress at stores, reads, mbarrier events, issues and collective events

A released pending thread performs its next event when it is

* a store without release semantics, the allocation's store of its address, or a read
  (`store_next_steps`, `allocStore_next_steps`, `read_next_steps`);
* an mbarrier initialization or arrival, with the object's checked record of it
  (`init_next_steps`, `arrive_next_steps`, through `Descent.object_steps_inOrder`): the record
  carries the transition's reply or its fault, so no readiness of the object is needed;
* the issue of a tensor copy (`tensorLoad_next_steps`, `Step.issue_counted_extension_reads`): the
  copy's effects are independent observations, none at issue;
* an MMA or a commit of one lane (`mma_next_steps`, `commit_next_steps`,
  `Step.tc_counted_extension_reads`): the completion and the deliveries are asynchronous
  obligations of their own;
* a Tensor Memory load, its wait, a store, its wait (`tcLoad_next_steps`, `tcStore_next_steps`),
  a named barrier (`bar_next_steps`) or a paired Tensor Memory operation (`tmem_next_steps`).

The safe prefix these extensions need is the order of the conflicts at the bytes that are read
(`NextSafe.reads`); none of them performs a commit arrive-on.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 100000

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The event of lane 0 of a recorded warp request is made by lane 0 of its warp. -/
theorem laneOf_event_zero (hX : Consistent L kernel asms mem0 X) {cta : Nat}
    {x : Tmem.Pair.Requests} (hx : x ∈ X.tmemHistory cta) : laneOf L (x.own.event L 0).1 = 0 := by
  obtain ⟨-, hw, -⟩ := ((hX.tmemPair.1 cta).1 x hx).2.2
  simp only [laneOf, Tmem.Pair.WarpRequest.event, Fin.val_zero, Nat.add_zero]
  rw [show x.own.cta * L.block + x.own.warp * 32 = x.own.warp * 32 + L.block * x.own.cta by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show x.own.warp * 32 < L.block by omega),
    Nat.mul_mod_left]

variable (hc : NextCtx Q L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
include hc hp

/-- **A released pending thread at a store to shared or global memory steps.** -/
theorem store_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .store) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, bs, u, rfl, hr⟩
  · exact ub_steps hc hp hrel hrun hl hout
  -- the thread's last event is no allocation request of lane 0: after one, lane 0 is at the
  -- address store
  have hres : Tmem.Pair.ResultOk L (X.snoc g ⟨t1.pc, .wr a bs⟩ (fun _ => none)) :=
    hX.tmemPairResult.snoc_last fun _ _ _ _ hget cta x hx hwi => by
      rcases hc.facts.alloc_next hp.1 hget hσ with h | h
      · rw [hk] at h
        cases h
      · have h0 := laneOf_event_zero hX hx
        rw [hwi] at h0
        exact h h0
  exact .inl (Step.plain_counted_extension hX hp.1 (.inr (launched hX g)) hrel hrun hl
    (o := some u) (e := ⟨t1.pc, .wr a bs⟩) ⟨_, hout, rfl, rfl⟩ hr (by simp [Kind.isTma, hr])
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    hres (snoc_wf hX))

/-- **A released pending thread at the allocation's address store steps**: it writes column 0, the
column every recorded allocation returns. The step is a counted extension, so every obligation
steps. -/
theorem allocStore_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .allocStore) (hrel : Step.Released L X g) {o : Descent.Obligation} :
    Sched.Steps (timed T Q L) mem0 X o := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨dst, u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  let e : Event := ⟨t1.pc, .wr { loc := dst, size := 4 }
    (Value.bits 32 (BitVec.ofNat 64 0)).toBytes⟩
  have hres : Tmem.Pair.ResultOk L (X.snoc g e (fun _ => none)) := by
    apply hX.tmemPairResult.snoc
    intro pc a bs he _ pc' grp dst' n hget cta x base hx hwi hwa
    simp only [e, Event.mk.injEq, Kind.wr.injEq] at he
    obtain ⟨-, -, rfl⟩ := he
    rw [hc.whole.alloc_base _ pc' grp dst' n cta x base hget hx hwi hwa]
  exact .inl (Step.plain_counted_extension hX hp.1 (.inr (launched hX g)) hrel hrun hl
    (o := some u) (e := e) ⟨_, hout, 0, by decide, rfl, rfl⟩ rfl (by simp [e, Kind.isTma])
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    hres (snoc_wf hX))

omit hc hp in
/-- **A read of a followed thread keeps the assumptions' constraints**, whatever bytes it takes
from sources (`NewRead`): the read-only input assumption by its own step
(`Interface.inputReadOnly_wf_read`, with `NextCtx.fresh`), the others under every in-order
extension (`asms_wf_others`). -/
theorem read_wf (hc : NextCtx Q L mem0 X) {g : Nat} (hg : g < L.threads) {s : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some s)) {t1 : TState}
    (hat : (threadCode L g Q).AtD s t1) (hinv : (threadCode L g Q).inv s) {a : Acc}
    {k : List (Option Byte) → TState} (hout : out kernel asms L g t1 = .ev (.read a k))
    {bs : List (Option Byte)} {r : Nat → Option AsyncCopy.Ref}
    (hread : ∀ e, NewRead L mem0 X g e r a bs) :
    ∀ a' ∈ asms, a'.wf L mem0 (X.snoc g ⟨t1.pc, .rd a bs⟩ r) := by
  have hX := hc.max.1
  have hF : (threadCode L g Q).toMachine.Fired (some s) ⟨t1.pc, .rd a bs⟩ (some (k bs)) := by
    refine ⟨t1, ⟨hat, hinv⟩, ?_⟩
    have ho := Code.site_out (hc.sound g hg) ⟨hat, hinv⟩
    rw [hout] at ho
    have ht : (threadCode L g Q).toMachine.tmpl (some s) t1 = .read a k := by
      injection ho with ho
      exact ho.symm
    rw [ht]
    exact ⟨bs, (hread ⟨t1.pc, .rd a bs⟩).len, rfl, rfl⟩
  intro a' ha'
  by_cases hne : a' = Assumptions.inputReadOnly
  · subst hne
    exact inputReadOnly_wf_read (hX.asm _ ha') (hread ⟨t1.pc, .rd a bs⟩)
      fun hs => hc.fresh hg hσ hF hs
  · exact asms_wf_others hX le_snoc (Execution.notifiedInOrder_of_eq rfl) a' ha' hne

/-- **A released pending thread at a read steps.** -/
theorem read_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .read) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide) (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, hat, hout, hm⟩ := next_fire hc hp hσ
  obtain ⟨-, -, -, -, hinv, -, -⟩ := Frame.end_at (C := code L Q) hc.sound hp.1 hrun hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, k, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.read_source_counted_extension hX hp.1 hne hrel hrun hl hout
      (fun _ _ hread => read_wf hc hp.1 hσ hat hinv hout hread) hc.guard)

/-- **A released pending thread at an mbarrier initialization steps.** -/
theorem init_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .init) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨l, c, u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · refine Descent.object_steps_inOrder asms_wfStep hX hc.whole.reads hc.guard
      (fun _ _ _ _ => no_release hX) (no_release_rmw hX) (no_threadFence hX) hp.1
      (.inr (launched hX g)) hrel hrun hl hout ⟨rfl, rfl⟩
      (.inr ⟨l, c, rfl⟩) (mb := l)
      (act := .init c) (fun _ _ h => by cases h) fun l' => ?_
    by_cases h : l' = l
    · subst h
      simp [objectAction, snoc_get_new]
    · simp [objectAction, snoc_get_new, h, Ne.symm h]

/-- **A released pending thread at an mbarrier arrival steps.** -/
theorem arrive_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .arrive) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨l, tx, u, c, rl, sc, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · refine Descent.object_steps_inOrder asms_wfStep hX hc.whole.reads hc.guard
      (fun _ _ _ _ => no_release hX) (no_release_rmw hX) (no_threadFence hX) hp.1
      (.inr (launched hX g)) hrel hrun hl hout ⟨rfl, rfl⟩
      (.inl ⟨l, tx, c, rl, sc, rfl⟩) (mb := l) (act := .arrive c tx) (fun _ _ h => by cases h)
      fun l' => ?_
    by_cases h : l' = l
    · subst h
      simp [objectAction, snoc_get_new]
    · simp [objectAction, snoc_get_new, h, Ne.symm h]

omit hc hp in
/-- The guard of an extension by an event that is no write, atomic, fence or poll. -/
theorem guard_snoc (hc : NextCtx Q L mem0 X) {g : Nat} {e : Event}
    (h1 : ∀ a bs, e.kind ≠ .wr a bs) (h2 : ∀ a o n, e.kind ≠ .rmw a o n)
    (h3 : ∀ sem s, e.kind ≠ .fence sem s)
    (h4 : ∀ pc m q acq sc, e = ⟨pc, .wait m q true acq sc⟩ → ∃ exit, kernel.CanonicalSpin pc exit) :
    SyncGuarded L kernel (X.snoc g e (fun _ => none)) :=
  hc.guard.snoc (fun _ _ _ _ => no_release hc.max.1) (no_release_rmw hc.max.1)
    (no_threadFence hc.max.1) h1 h2 h3 h4

/-- **A released pending thread at a tensor copy issue steps.** -/
theorem tensorLoad_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .tensorLoad) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide) (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, sp, u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.issue_counted_extension_reads hX hc.whole.reads hp.1 hne hrel hrun hl
      (e := ⟨t1.pc, .tensorIssue a sp⟩) (o := some u) ⟨_, hout, rfl, rfl⟩ (.inl ⟨a, sp, rfl⟩)
      (snoc_wf hX) (guard_snoc hc nofun nofun nofun nofun))

/-- **A released pending thread at an MMA steps.** -/
theorem mma_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .mma) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide) (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨dc, sp, acc, ms, u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.tc_counted_extension_reads hX hc.whole.reads hp.1 hne hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (snoc_wf hX) (guard_snoc hc nofun nofun nofun nofun))

/-- **A released pending thread at a commit steps.** -/
theorem commit_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .commit) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide) (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨sp, u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.tc_counted_extension_reads hX hc.whole.reads hp.1 hne hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (snoc_wf hX) (guard_snoc hc nofun nofun nofun nofun))

/-- **A released pending thread at a Tensor Memory load or its wait steps.** -/
theorem tcLoad_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .tcLoad) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide) (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, n, sh, k, rfl⟩ | ⟨u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · refine .inl (Step.tc_load_counted_extension hX hp.1 hne hrel hrun hl
      (o := some (k (Step.loadVals L asms X g sh a n)))
      ⟨_, hout, _, Step.loadVals_length, rfl, rfl⟩ ?_ (snoc_wf hX))
    intro j v hj hv
    rw [Step.loadVals_length] at hj
    refine ⟨Step.loadVals_spec hX hc.guard hc.layout hj hv, ?_⟩
    obtain ⟨s, hs, -⟩ := hv
    exact hc.whole.words _ _ _ hs
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inr (launched hX g)) hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
      (hX.tcRead_snoc_tc nofun) (snoc_wf hX))

/-- **A released pending thread at a Tensor Memory store or its wait steps.** -/
theorem tcStore_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .tcStore) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, vs, sh, u, rfl⟩ | ⟨u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inr (launched hX g)) hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
      (hX.tcRead_snoc_tc nofun) (snoc_wf hX))
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inr (launched hX g)) hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
      (hX.tcRead_snoc_tc nofun) (snoc_wf hX))

/-- **A released pending thread at a named-barrier arrival steps.** -/
theorem bar_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .bar) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨id, u, c, md, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.barArrival_counted_extension hX hp.1 (.inr (launched hX g)) hrel
      (snoc_wf hX) hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩)

/-- **A released pending thread at a paired Tensor Memory operation steps.** -/
theorem tmem_next_steps {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .tmem) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨grp, dst, act, u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inr (launched hX g)) hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
      (hX.tcRead_snoc_tc fun _ _ _ h => by cases h) (snoc_wf hX))

end

end PTX.Kernels.InklingRelDecode.Proof.Progress

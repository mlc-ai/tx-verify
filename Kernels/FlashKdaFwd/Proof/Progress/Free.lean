-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Progress.Wf
public import Lemmas.Kernel.Progress.Released

@[expose] public section

/-!
# A released thread at an event that needs no partner, under `WfStepE`

Kernel-independent restatements of library theorems (candidates for
`Lemmas/Kernel/Progress/Released.lean`, `Lemmas/Kernel/NextReads.lean`,
`Lemmas/Kernel/NextInOrder.lean`). The originals take `Assumption.WfStep`, which a kernel with
an assumption about elections cannot prove (`Wf.lean`). Each theorem here has the original's
statement with `WfStepE` in its place, and the original's proof: the extension it builds
appends one event that reads no memory and is no election, so the assumptions' constraints
survive it (`WfStepE.snoc`, `WfStepE.snocObject`).

* `ub_stepsE`, `dead_stepsE`: a released thread whose run reaches undefined behaviour, or whose
  machine has stopped, performs the undefined behaviour (`Descent.ub_steps_inOrder`,
  `Descent.dead_steps_inOrder`).
* `quiet_kind_stepsE`, `object_stepsE`: a fence or a bulk commit; an mbarrier initialization or
  arrival (`Descent.quiet_steps_inOrder`, `Descent.object_steps_inOrder`).
* `NextEnvE` and the per-template steps `exit_stepsE`, `quiet_stepsE`, `arrive_stepsE`,
  `init_stepsE`, `tensorLoad_stepsE`, `tensorStore_stepsE`, `bar_stepsE`, `bulkWait_stepsE`,
  `read_stepsE`, `store_stepsE` (`Descent.NextEnv` and its theorems). The environment has no
  Tensor Core fields: the steps of Tensor Core instructions are not restated.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Flow PTX.Descent MBarrier AsyncCopy

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}
variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- **A released thread whose template is undefined behaviour steps.** -/
theorem ub_stepsE (hA : WfStepE sel L K mem0 A) (hX : Consistent L K A mem0 X) {g : Nat}
    (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hrel : Step.Released L X g) {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {f : Fault}
    (hout : out K A L g t1 = .ev (.ub f)) : Steps L K A mem0 Obl rank X o :=
  .inl (Step.plain_counted_extension hX hg hne hrel hrun hl (o := none) ⟨_, hout, rfl, rfl⟩
    trivial rfl nofun nofun nofun rfl (hX.tmemPairResult.snoc_not_wr nofun)
    (hA.snoc hX rfl rfl))

/-- **A released pending thread whose machine stopped steps.** -/
theorem dead_stepsE {C : (g : Nat) → Flow.Code K A L g} (hA : WfStepE sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) {h : Nat}
    (hC : ∀ g < L.threads, (C g).Sound) (hp : Frame.Pending L X h)
    (hσ : Frame.stateAt C X h (X.tr h).length = none) (hrel : Step.Released L X h) :
    Steps L K A mem0 Obl rank X o := by
  have hX := hmax.1
  obtain ⟨u, hrun⟩ := Frame.run_some hX hub hp
  have hne : X.tr h ≠ [] := by
    rintro hnil
    rw [hnil, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  exact .inl (Step.dead_counted_extension hX hp.1 hne hrel
    (fun _ _ => hA.snoc hX rfl rfl) hrun (Frame.end_dead hC hp.1 hrun hσ))

/-- **A released thread performs a proxy fence, an mbarrier-initialization fence, a CLC response
query or a bulk commit.** -/
theorem quiet_kind_stepsE (hA : WfStepE sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X) (hsg : SyncGuarded L K X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s)
    {g : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hrel : Step.Released L X g)
    {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl} {k : Kind} {u : TState}
    (hout : out K A L g t1 = .ev m) (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
    (hk : (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ (∃ q r, k = .clcQuery q r) ∨
      k = .bulkCommit) :
    Steps L K A mem0 Obl rank X o := by
  refine .inl (Step.quiet_counted_extension_reads hX hord hg hne hrel hrun hl ⟨_, hout, hf⟩ ?_ ?_
    (Step.objectAction_snoc_new ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hA.snoc hX ?_ ?_)
    (hsg.snoc hnr hnrmw hnf ?_ ?_ ?_ ?_)) <;>
  rcases hk with ⟨f, s, rfl⟩ | rfl | ⟨q, r, rfl⟩ | rfl <;>
    first | trivial | (intros; simp_all)

/-- **A released thread initializes or arrives on an mbarrier.** -/
theorem object_stepsE (hA : WfStepE sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X) (hsg : SyncGuarded L K X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s)
    {g : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hrel : Step.Released L X g)
    {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl} {k : Kind} {u : TState}
    (hout : out K A L g t1 = .ev m) (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
    (hk : (∃ l tx c rl sc, k = .arrive l tx c rl sc) ∨ ∃ l c, k = .mbInit l c)
    {mb : Loc} {act : Action} (hnp : ∀ p ok, act ≠ .pollParity p ok)
    (hact : ∀ l, objectAction (X.snoc g ⟨t1.pc, k⟩ (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = mb then some act else none) :
    Steps L K A mem0 Obl rank X o := by
  refine .inl (Step.object_counted_extension_reads hX hord hg hne hrel hrun hl ⟨_, hout, hf⟩
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hnp hact
    (fun _ => hA.snocObject hX ?_ ?_)
    (fun _ hw => hsg.snocObject hnr hnrmw hnf ?_ ?_ ?_ ?_ hw)) <;>
  rcases hk with ⟨l, tx, c, rl, sc, rfl⟩ | ⟨l, c, rfl⟩ <;>
    first
      | exact Kind.WaitFree.mk trivial (fun _ h => by cases h)
      | trivial
      | (intros; simp_all)

/-! ### The environment and the steps of each template -/

/-- **What the steps of a released thread use of a maximal execution** (`Descent.NextEnv`
without its Tensor Core fields, and with `WfStepE`). -/
structure NextEnvE (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0)
    (X : Execution) : Prop where
  max : Maximal L K A mem0 X
  noUb : ¬ HasUb X
  wf : WfStepE (fun _ => true) L K mem0 A
  readWf : ∀ g pc a bs r, (∀ e, NewRead L mem0 X g e r a bs) →
    ∀ a' ∈ A, a'.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r)
  reads : ReadsOrdered L X
  guard : SyncGuarded L K X
  no_release : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  no_release_rmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false
  no_fence : ∀ e sem s, ¬ X.ThreadFence e sem s

variable (hc : NextEnvE L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) (hne : X.tr g ≠ [])
  (hrel : Step.Released L X g) {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
  (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl} (hout : out K A L g t1 = .ev m)
include hc hp hne hrel hrun hl hout

theorem exit_stepsE (hm : KindTmpl .exit m) : Steps L K A mem0 Obl rank X o := by
  subst hm
  exact .inl (Step.plain_counted_extension hc.max.1 hp.1 (.inl hne) hrel hrun hl (o := none)
    (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    (hc.max.1.tmemPairResult.snoc_not_wr nofun) (hc.wf.snoc hc.max.1 rfl rfl))

theorem quiet_stepsE (hm : KindTmpl .quiet m) : Steps L K A mem0 Obl rank X o := by
  have hq := fun {k : Kind} {u : TState} (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
      (hk : (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ (∃ q r, k = .clcQuery q r) ∨
        k = .bulkCommit) =>
    quiet_kind_stepsE (Obl := Obl) (rank := rank) (o := o) hc.wf hc.max.1 hc.reads hc.guard
      hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout hf hk
  rcases hm with ⟨k, o', u, rfl⟩ | ⟨u, rfl⟩ | ⟨q, r, u, rfl⟩ | ⟨u, rfl⟩
  · exact hq ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
  · exact hq ⟨rfl, rfl⟩ (.inr (.inl rfl))
  · exact hq ⟨rfl, rfl⟩ (.inr (.inr (.inl ⟨_, _, rfl⟩)))
  · exact hq ⟨rfl, rfl⟩ (.inr (.inr (.inr rfl)))

theorem arrive_stepsE (hm : KindTmpl .arrive m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨l, tx, u, c, rl, sc, rfl⟩ := hm
  refine object_stepsE hc.wf hc.max.1 hc.reads hc.guard
    hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
    (.inl ⟨l, tx, c, rl, sc, rfl⟩) (mb := l) (act := .arrive c tx) (fun _ _ h => by cases h)
    fun l' => ?_
  by_cases h : l' = l
  · subst h
    simp [objectAction, snoc_get_new]
  · simp [objectAction, snoc_get_new, h, Ne.symm h]

theorem init_stepsE (hm : KindTmpl .init m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨l, c, u, rfl⟩ := hm
  refine object_stepsE hc.wf hc.max.1 hc.reads hc.guard
    hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
    (.inr ⟨l, c, rfl⟩) (mb := l) (act := .init c) (fun _ _ h => by cases h) fun l' => ?_
  by_cases h : l' = l
  · subst h
    simp [objectAction, snoc_get_new]
  · simp [objectAction, snoc_get_new, h, Ne.symm h]

theorem tensorLoad_stepsE (hm : KindTmpl .tensorLoad m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, s, u, rfl⟩ := hm
  exact .inl (Step.issue_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (e := ⟨t1.pc, .tensorIssue a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩ (.inl ⟨a, s, rfl⟩)
    (hc.wf.snoc hc.max.1 rfl rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem tensorStore_stepsE (hm : KindTmpl .tensorStore m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, s, u, rfl⟩ := hm
  exact .inl (Step.issue_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (e := ⟨t1.pc, .tensorStore a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩
    (.inr (.inl ⟨a, s, rfl⟩)) (hc.wf.snoc hc.max.1 rfl rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem bar_stepsE (hm : KindTmpl .bar m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨id, u, c, md, rfl⟩ := hm
  exact .inl (Step.barArrival_counted_extension hc.max.1 hp.1 (.inl hne) hrel
    (hc.wf.snoc hc.max.1 rfl rfl) hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩)

theorem bulkWait_stepsE (hm : KindTmpl .bulkWait m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨mode, n, u, rfl⟩ := hm
  exact .inl (Step.BulkWait.bulk_wait_counted_extension hc.max.1 hp.1 hne hrel
    (hc.wf.snoc hc.max.1 rfl rfl) hrun hl (u := u) ⟨_, hout, rfl, rfl⟩)

theorem read_stepsE (hm : KindTmpl .read m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, k, rfl⟩ := hm
  exact .inl (Step.read_source_counted_extension hc.max.1 hp.1 hne hrel hrun hl hout
    (fun bs r h => hc.readWf g t1.pc a bs r h) hc.guard)

/-- A store, when the thread's last event is no allocation request of lane 0 of its warp. -/
theorem store_stepsE (hm : KindTmpl .store m)
    (hlast : ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → laneOf L g ≠ 0) :
    Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, bs, u, rfl, hr⟩ := hm
  have hres : Tmem.Pair.ResultOk L (X.snoc g ⟨t1.pc, .wr a bs⟩ (fun _ => none)) :=
    hc.max.1.tmemPairResult.snoc_last fun _ _ _ _ hget cta x hx hwi => by
      have h0 := laneOf_event_zero hc.max.1 hx
      rw [hwi] at h0
      exact hlast _ _ _ _ hget h0
  exact .inl (Step.plain_counted_extension hc.max.1 hp.1 (.inl hne) hrel hrun hl (o := some u)
    (e := ⟨t1.pc, .wr a bs⟩) ⟨_, hout, rfl, rfl⟩ hr (by simp [Kind.isTma, hr])
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    hres (hc.wf.snoc hc.max.1 rfl rfl))

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress

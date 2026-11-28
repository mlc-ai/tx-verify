-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Released
public import Lemmas.Quiet.Progress.ReleasedU

@[expose] public section

/-! # A released thread steps under quiet extensions, with no premise on reads

`Descent.NextEnvQ` asks the assumptions' constraints of every read appended to the execution
(`readWf`). A kernel whose assumptions constrain some reads (a read-only input tensor) cannot
give it. `NextEnvG` is `NextEnvQ` without it, and the steps of every kind but `read` are the
library's: `released_stepsUG` is `released_stepsUQ` at an instruction that is no plain read.
A plain read is appended by `Step.read_source_counted_extension`, whose premise is the
constraints of the read at its own address. -/

namespace PTX.Descent
open PTX PTX.Flow MBarrier AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **What the steps of a released thread use of a maximal execution**: no undefined behaviour,
assumptions whose constraints survive the extensions without a commit arrive-on and survive a
read with a source, the order of the conflicts at the bytes that are read, synchronization kept
guarded (no releasing write, no thread fence), injective MMA layouts and 4-byte Tensor Memory
words. -/
structure NextEnvG (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0)
    (X : Execution) : Prop where
  max : Maximal L K A mem0 X
  noUb : ¬ HasUb X
  wf : Assumption.WfQuiet (fun _ => true) L K mem0 A
  reads : ReadsOrdered L X
  guard : SyncGuarded L K X
  no_release : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  no_release_rmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false
  no_fence : ∀ e sem s, ¬ X.ThreadFence e sem s
  layout : TcMma.LayoutInjective X
  words : ∀ s cell v, TcMma.Wrote L A X s cell v → v.bytes = 4

/-- An extension by an event that is neither a read nor an exit keeps the assumptions'
constraints. -/
theorem NextEnvG.snoc_wf (hc : NextEnvG L K A mem0 X) {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (h : e.kind.readsMem = false)
    (hx : e.kind.isExit = false := by exact rfl) :
    ∀ a ∈ A, a.wf L mem0 (X.snoc g e r) :=
  hc.wf.quiet hc.max.1 le_snoc rfl (Execution.quietExt_snoc h hx)

variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

variable {C : (g : Nat) → Flow.Code K A L g}

theorem next_classUG (hc : NextEnvG L K A mem0 X) (hC : ∀ g < L.threads, (C g).SoundU) {g : Nat}
    (hp : Frame.Pending L X g) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g) {k : NextKind}
    (hk : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op = k)
    (h : ∀ t t1 m, Run K A L g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau K A L g) t t1 → out K A L g t1 = .ev m → KindTmpl k m →
      Steps L K A mem0 Obl rank X o) :
    Steps L K A mem0 Obl rank X o := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hsite | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrderQ hc.wf hc.max.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := hsite
  rcases tmpl_kind (A := A) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_steps_inOrderQ hc.wf hc.max.1 hp.1 hne hrel hrun hl hout
  · rw [hk ins hins] at hm
    exact h t t1 _ hrun hl hout hm

section Kinds

variable (hc : NextEnvG L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) (hne : X.tr g ≠ [])
  (hrel : Step.Released L X g) {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
  (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl} (hout : out K A L g t1 = .ev m)

include hc hp hne hrel hrun hl hout

/-- **The exit**, when the assumptions' constraints hold of the execution with the thread's exit
appended. -/
theorem exit_stepsG (hexit : ∀ pc r, ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .exit⟩ r))
    (hm : KindTmpl .exit m) : Steps L K A mem0 Obl rank X o := by
  subst hm
  exact .inl (Step.plain_counted_extension hc.max.1 hp.1 (.inl hne) hrel hrun hl (o := none)
    (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    (hc.max.1.tmemPairResult.snoc_not_wr nofun) (hexit _ _))

theorem quiet_stepsG (hm : KindTmpl .quiet m) : Steps L K A mem0 Obl rank X o := by
  have hq := fun {k : Kind} {u : TState} (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
      (hk : (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ (∃ q r, k = .clcQuery q r) ∨
        k = .bulkCommit) =>
    quiet_steps_inOrderQ (Obl := Obl) (rank := rank) (o := o) hc.wf hc.max.1 hc.reads hc.guard
      hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout hf hk
  rcases hm with ⟨k, o', u, rfl⟩ | ⟨u, rfl⟩ | ⟨q, r, u, rfl⟩ | ⟨u, rfl⟩
  · exact hq ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
  · exact hq ⟨rfl, rfl⟩ (.inr (.inl rfl))
  · exact hq ⟨rfl, rfl⟩ (.inr (.inr (.inl ⟨_, _, rfl⟩)))
  · exact hq ⟨rfl, rfl⟩ (.inr (.inr (.inr rfl)))

theorem arrive_stepsG (hm : KindTmpl .arrive m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨l, tx, u, c, rl, sc, rfl⟩ := hm
  refine object_steps_inOrderQ hc.wf hc.max.1 hc.reads hc.guard
    hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
    (.inl ⟨l, tx, c, rl, sc, rfl⟩) (mb := l) (act := .arrive c tx) (fun _ _ h => by cases h)
    fun l' => ?_
  by_cases h : l' = l
  · subst h
    simp [objectAction, snoc_get_new]
  · simp [objectAction, snoc_get_new, h, Ne.symm h]

theorem tensorLoad_stepsG (hm : KindTmpl .tensorLoad m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, s, u, rfl⟩ := hm
  exact .inl (Step.issue_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (e := ⟨t1.pc, .tensorIssue a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩ (.inl ⟨a, s, rfl⟩)
    (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem tensorStore_stepsG (hm : KindTmpl .tensorStore m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, s, u, rfl⟩ := hm
  exact .inl (Step.issue_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (e := ⟨t1.pc, .tensorStore a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩
    (.inr (.inl ⟨a, s, rfl⟩)) (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem mma_stepsG (hm : KindTmpl .mma m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨dc, s, acc, ms, u, rfl⟩ := hm
  exact .inl (Step.tc_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem commit_stepsG (hm : KindTmpl .commit m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨s, u, rfl⟩ := hm
  exact .inl (Step.tc_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem cluster_stepsG (hm : KindTmpl .cluster m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨op, u, rfl⟩ := hm
  exact .inl (Step.cluster_counted_extension hc.max.1 hp.1 hne hrel (hc.snoc_wf rfl) hrun hl
    (o := some u) ⟨_, hout, rfl, rfl⟩)

theorem bar_stepsG (hm : KindTmpl .bar m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨id, u, c, md, rfl⟩ := hm
  exact .inl (Step.barArrival_counted_extension hc.max.1 hp.1 (.inl hne) hrel (hc.snoc_wf rfl)
    hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩)

theorem tmem_stepsG (hm : KindTmpl .tmem m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨grp, act, u, rfl, -⟩ := hm
  exact .inl (Step.tccoll_counted_extension hc.max.1 hp.1 (.inl hne) hrel hrun hl (o := some u)
    ⟨_, hout, rfl, rfl⟩ rfl (hc.max.1.tmemPairResult.snoc_not_wr nofun)
    (hc.max.1.tcRead_snoc_tc fun _ _ _ h => by cases h) (hc.snoc_wf rfl))

theorem bulkWait_stepsG (hm : KindTmpl .bulkWait m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨mode, n, u, rfl⟩ := hm
  exact .inl (Step.BulkWait.bulk_wait_counted_extension hc.max.1 hp.1 hne hrel (hc.snoc_wf rfl)
    hrun hl (u := u) ⟨_, hout, rfl, rfl⟩)

theorem tcLoad_stepsG (hm : KindTmpl .tcLoad m) : Steps L K A mem0 Obl rank X o := by
  rcases hm with ⟨a, n, sh, k, rfl⟩ | ⟨u, rfl⟩
  · refine .inl (Step.tc_load_counted_extension hc.max.1 hp.1 hne hrel hrun hl
      (o := some (k (Step.loadVals L A X g sh a n)))
      ⟨_, hout, _, Step.loadVals_length, rfl, rfl⟩ ?_ (hc.snoc_wf rfl))
    intro j v hj hv
    rw [Step.loadVals_length] at hj
    refine ⟨Step.loadVals_spec hc.max.1 hc.guard hc.layout hj hv, ?_⟩
    obtain ⟨s, hs, -⟩ := hv
    exact hc.words _ _ _ hs
  · exact .inl (Step.tccoll_counted_extension hc.max.1 hp.1 (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ rfl (hc.max.1.tmemPairResult.snoc_not_wr nofun)
      (hc.max.1.tcRead_snoc_tc nofun) (hc.snoc_wf rfl))

/-- A store, when the thread's last event is no allocation request of lane 0 of its warp. -/
theorem store_stepsG (hm : KindTmpl .store m)
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
    hres (hc.snoc_wf rfl))

theorem init_stepsG (hm : KindTmpl .init m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨l, c, u, rfl⟩ := hm
  refine object_steps_inOrderQ hc.wf hc.max.1 hc.reads hc.guard
    hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
    (.inr ⟨l, c, rfl⟩) (mb := l) (act := .init c) (fun _ _ h => by cases h) fun l' => ?_
  by_cases h : l' = l
  · subst h
    simp [objectAction, snoc_get_new]
  · simp [objectAction, snoc_get_new, h, Ne.symm h]

end Kinds

section Released

variable (hc : NextEnvG L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)

include hc hp hne hrel

theorem released_stepsUG (hC : ∀ g < L.threads, (C g).SoundU) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d))
    (hk : ∀ ins, K.code[(C g).pc d]? = some ins → (opKind ins.op).Rest = false)
    (hnr : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op ≠ .read)
    (hlast : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op = .store →
      ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → laneOf L g ≠ 0)
    (hexit : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op = .exit →
      ∀ pc r, ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .exit⟩ r)) :
    Steps L K A mem0 Obl rank X o := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hsite | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrderQ hc.wf hc.max.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, -, -, -, hins, -⟩ := hsite
  have hr := hk ins hins
  have hk' : ∀ ins', K.code[(C g).pc d]? = some ins' → opKind ins'.op = opKind ins.op := by
    intro ins' h'
    rw [hins] at h'
    cases h'
    rfl
  generalize hkd : opKind ins.op = k at hr hk'
  refine next_classUG hc hC hp hσ hne hrel hk' fun t t1 m hrun hl hout hm => ?_
  cases k
  case wait | warp | reg | alloc | other => simp [NextKind.Rest] at hr
  case cluster => exact cluster_stepsG hc hp hne hrel hrun hl hout hm
  case bar => exact bar_stepsG hc hp hne hrel hrun hl hout hm
  case tmem => exact tmem_stepsG hc hp hne hrel hrun hl hout hm
  case init => exact init_stepsG hc hp hne hrel hrun hl hout hm
  case arrive => exact arrive_stepsG hc hp hne hrel hrun hl hout hm
  case tensorLoad => exact tensorLoad_stepsG hc hp hne hrel hrun hl hout hm
  case tensorStore => exact tensorStore_stepsG hc hp hne hrel hrun hl hout hm
  case mma => exact mma_stepsG hc hp hne hrel hrun hl hout hm
  case commit => exact commit_stepsG hc hp hne hrel hrun hl hout hm
  case bulkWait => exact bulkWait_stepsG hc hp hne hrel hrun hl hout hm
  case tcLoad => exact tcLoad_stepsG hc hp hne hrel hrun hl hout hm
  case read => exact absurd hkd (hnr ins hins)
  case quiet => exact quiet_stepsG hc hp hne hrel hrun hl hout hm
  case store => exact store_stepsG hc hp hne hrel hrun hl hout hm (hlast ins hins hkd)
  case exit => exact exit_stepsG hc hp hne hrel hrun hl hout (hexit ins hins hkd) hm

end Released

end

end PTX.Descent

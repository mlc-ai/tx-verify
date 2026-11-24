-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.NextReads
public import Lemmas.Kernel.Frame
public import Lemmas.Flow.Fire
public import Lemmas.Step.ReadSource
public import Lemmas.Step.TcLoad
public import Lemmas.Step.BulkWaitReady
public import Lemmas.Step.BarArrival

@[expose] public section

/-! # A released thread at a step that needs no partner performs it

A proof tool, generic over the kernel (the kernel-independent part of FlashAttention-4's
`Progress/Next*.lean`, whose per-kernel `NextFacts.fire` it replaces by `Frame.end_at`).

A pending thread of a maximal execution without undefined behaviour, followed by a sound code
machine to a state `d`, reaches by local steps a concrete state of `d` whose template is the event
of the instruction at `d`'s site (`Frame.end_at`): undefined behaviour or an event of the
instruction's class (`Flow.eventTmpl_opTmpl`). The class picks the step (`opKind`, `KindTmpl`,
`tmpl_kind`). When the thread is released (its last blocking event, if any, is ready), it
performs:

* undefined behaviour, the exit, a fence, a bulk commit, a CLC response query;
* an mbarrier initialization or arrival with the object's checked record of it;
* the issue of a tensor copy or store, an MMA, a Tensor Core commit, a cluster barrier operation;
* a named-barrier arrival (`bar.sync`, `bar.arrive`): the arrival is appended, the wait for the
  barrier is a later blocking;
* a deallocation or relinquishment of Tensor Memory, a bulk-group wait (whose readiness is a
  later blocking);
* a read, with a source at each byte that no write it sees hides, when the assumptions' constraint
  survives the read (`NextEnv.readWf`);
* a store without release semantics, when the allocator's result rule survives it
  (`NextEnv.storeOk`);
* a Tensor Memory load or its wait, when the Tensor Memory cells hold 4-byte words and the MMA
  layouts are injective (`NextEnv.words`, `NextEnv.layout`).

`released_steps` is the dispatch. The kinds outside it (`NextKind.Rest`) are the classes that
need a partner or a kernel fact: an mbarrier poll (its blocker), a warp collective (the other
lanes), a register request (the kernel's entry), an allocation (the allocator's column), and
instructions without a class. The extensions perform no commit arrive-on, so the assumptions'
constraints survive them (`Assumption.WfStep.quiet`). -/

namespace PTX.Descent

open PTX PTX.Flow MBarrier AsyncCopy

noncomputable section

/-- The class of an instruction's event. -/
inductive NextKind where
  | wait | warp | cluster | bar | reg | alloc | tmem | init | arrive | tensorLoad | tensorStore
  | mma | commit | bulkWait | tcLoad | read | quiet | store | exit | other
  deriving DecidableEq

/-- **The class of an instruction.** -/
def opKind : Op → NextKind
  | .ret | .exit => .exit
  | .mem a => match a.kind, a.sem, a.nc with
    | .load, .weak, false | .load, .acquire, false => .read
    | .store, .weak, _ => .store
    | _, _, _ => .other
  | .fence (.proxy ..) | .fenceMbarInit | .bulkCommit | .clcQuery .. => .quiet
  | .mbarInit .. => .init
  | .mbarArrive .. => .arrive
  | .mbarWait .. => .wait
  | .bulkWait .. => .bulkWait
  | .cpTensor .. => .tensorLoad
  | .cpTensorStore .. => .tensorStore
  | .tcCommit .. => .commit
  | .tcMma .. => .mma
  | .tcLd .. | .tcWaitLd => .tcLoad
  | .tcAlloc .. => .alloc
  | .tcDealloc .. | .tcRelinquish .. => .tmem
  | .cluster _ => .cluster
  | .barSync .. | .barSyncN .. | .barArrive .. => .bar
  | .setMaxReg .. => .reg
  | .warp _ => .warp
  | _ => .other

/-- The kinds `released_steps` does not perform. -/
def NextKind.Rest : NextKind → Bool
  | .wait | .warp | .reg | .alloc | .other => true
  | _ => false

/-- The templates of each kind, apart from undefined behaviour. -/
def KindTmpl : NextKind → Tmpl → Prop
  | .exit, m => m = .exit
  | .read, m => ∃ a k, m = .read a k
  | .store, m => ∃ a bs t, m = .write a bs t ∧ a.release = false
  | .quiet, m => (∃ k o t, m = .fenceProxy k o t) ∨ (∃ t, m = .fenceMbarInit t) ∨
    (∃ q r t, m = .clcQuery q r t) ∨ ∃ t, m = .bulkCommit t
  | .init, m => ∃ l c t, m = .mbInit l c t
  | .arrive, m => ∃ l tx t c r s, m = .arrive l tx t c r s
  | .bulkWait, m => ∃ md n t, m = .bulkWait md n t
  | .tensorLoad, m => ∃ a s t, m = .tensorIssue a s t
  | .tensorStore, m => ∃ a s t, m = .tensorStore a s t
  | .commit, m => ∃ s t, m = .tc (.commit s) t
  | .mma, m => ∃ d s acc ms t, m = .tc (.mma d s acc ms) t
  | .tcLoad, m => (∃ a n sh k, m = .tcLd a n sh k) ∨ ∃ t, m = .tc .waitLd t
  | .tmem, m => ∃ grp act t, m = .tc (.resource grp none act) t ∧ ∀ n, act ≠ .alloc n
  | .cluster, m => ∃ op t, m = .cluster op t
  | .bar, m => ∃ id t c md, m = .bar id t c md
  | _, _ => True

/-- **An event of an instruction's class is of its kind.** -/
theorem opEv_kind {L : Launch} {g : Nat} {op : Op} {m : Tmpl} (h : OpEv L g op m) :
    KindTmpl (opKind op) m := by
  cases op
  case cluster => obtain ⟨t, rfl⟩ := h; exact ⟨_, _, rfl⟩
  case fence f =>
    cases f <;> simp only [OpEv, opKind, KindTmpl] at h ⊢
    obtain ⟨t, rfl⟩ := h; exact .inl ⟨_, _, _, rfl⟩
  case mem a =>
    simp only [OpEv, opKind] at h ⊢
    revert h
    cases a.kind <;> cases a.sem <;> cases a.nc <;> simp [KindTmpl]
    intro x y h _; exact ⟨x, y, h⟩
  all_goals simp only [OpEv, opKind, KindTmpl] at h ⊢
  all_goals first
    | trivial
    | exact .inr h
    | exact .inr (.inr (.inl h))
    | exact .inr (.inr (.inr h))
    | (obtain ⟨t, rfl⟩ := h; simp)
    | (obtain ⟨id, t, c, rfl⟩ := h; exact ⟨_, _, _, _, rfl⟩)

/-- **The template at a concrete state is undefined behaviour or of its instruction's kind.** -/
theorem tmpl_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState} (op : Op) :
    (∃ f, eventTmpl A L g t op = .ub f) ∨ KindTmpl (opKind op) (eventTmpl A L g t op) := by
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t) op with h | h
  · exact .inl h
  · exact .inr (opEv_kind h)

/-! ### What a step of a released thread uses -/

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **What the steps of a released thread use of a maximal execution**: no undefined behaviour,
assumptions whose constraints survive the extensions without a commit arrive-on and survive a
read with a source, the order of the conflicts at the bytes that are read, synchronization kept
guarded (no releasing write, no thread fence), injective MMA layouts and 4-byte Tensor Memory
words. -/
structure NextEnv (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0)
    (X : Execution) : Prop where
  max : Maximal L K A mem0 X
  noUb : ¬ HasUb X
  wf : Assumption.WfStep (fun _ => true) L K mem0 A
  readWf : ∀ g pc a bs r, (∀ e, NewRead L mem0 X g e r a bs) →
    ∀ a' ∈ A, a'.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r)
  reads : ReadsOrdered L X
  guard : SyncGuarded L K X
  no_release : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  no_release_rmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false
  no_fence : ∀ e sem s, ¬ X.ThreadFence e sem s
  layout : TcMma.LayoutInjective X
  words : ∀ s cell v, TcMma.Wrote L A X s cell v → v.bytes = 4

/-- The event of lane 0 of a recorded warp request is made by lane 0 of its warp. -/
theorem laneOf_event_zero (hX : Consistent L K A mem0 X) {cta : Nat}
    {x : Tmem.Pair.Requests} (hx : x ∈ X.tmemHistory cta) : laneOf L (x.own.event L 0).1 = 0 := by
  obtain ⟨-, hw, -⟩ := ((hX.tmemPair.1 cta).1 x hx).2.2
  simp only [laneOf, Tmem.Pair.WarpRequest.event, Fin.val_zero, Nat.add_zero]
  rw [show x.own.cta * L.block + x.own.warp * 32 = x.own.warp * 32 + L.block * x.own.cta by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show x.own.warp * 32 < L.block by omega),
    Nat.mul_mod_left]

variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- An extension by an event that reads no memory keeps the assumptions' constraints. -/
theorem NextEnv.snoc_wf (hc : NextEnv L K A mem0 X) {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (h : e.kind.readsMem = false) :
    ∀ a ∈ A, a.wf L mem0 (X.snoc g e r) :=
  hc.wf.quiet hc.max.1 le_snoc rfl (Execution.noNewRead_snoc h)

/-! ### The steps of each kind -/

variable {C : (g : Nat) → Flow.Code K A L g}

/-- **A released pending thread followed to a state whose instruction is of kind `k`** steps
when it steps at every template of kind `k` that a concrete state of it reaches; a template of
undefined behaviour is performed. -/
theorem next_class (hc : NextEnv L K A mem0 X) (hC : ∀ g < L.threads, (C g).Sound) {g : Nat}
    (hp : Frame.Pending L X g) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g) {k : NextKind}
    (hk : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op = k)
    (h : ∀ t t1 m, Run K A L g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau K A L g) t t1 → out K A L g t1 = .ev m → KindTmpl k m →
      Steps L K A mem0 Obl rank X o) :
    Steps L K A mem0 Obl rank X o := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := Frame.end_at hC hp.1 hrun hσ
  rcases tmpl_kind (A := A) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_steps_inOrder hc.wf hc.max.1 hp.1 hne hrel hrun hl hout
  · rw [hk ins hins] at hm
    exact h t t1 _ hrun hl hout hm

variable (hc : NextEnv L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) (hne : X.tr g ≠ [])
  (hrel : Step.Released L X g) {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
  (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl} (hout : out K A L g t1 = .ev m)
include hc hp hne hrel hrun hl hout

theorem exit_steps (hm : KindTmpl .exit m) : Steps L K A mem0 Obl rank X o := by
  subst hm
  exact .inl (Step.plain_counted_extension hc.max.1 hp.1 (.inl hne) hrel hrun hl (o := none)
    (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    (hc.max.1.tmemPairResult.snoc_not_wr nofun) (hc.snoc_wf rfl))

theorem quiet_steps' (hm : KindTmpl .quiet m) : Steps L K A mem0 Obl rank X o := by
  have hq := fun {k : Kind} {u : TState} (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
      (hk : (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ (∃ q r, k = .clcQuery q r) ∨
        k = .bulkCommit) =>
    quiet_steps_inOrder (Obl := Obl) (rank := rank) (o := o) hc.wf hc.max.1 hc.reads hc.guard
      hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout hf hk
  rcases hm with ⟨k, o', u, rfl⟩ | ⟨u, rfl⟩ | ⟨q, r, u, rfl⟩ | ⟨u, rfl⟩
  · exact hq ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
  · exact hq ⟨rfl, rfl⟩ (.inr (.inl rfl))
  · exact hq ⟨rfl, rfl⟩ (.inr (.inr (.inl ⟨_, _, rfl⟩)))
  · exact hq ⟨rfl, rfl⟩ (.inr (.inr (.inr rfl)))

theorem arrive_steps (hm : KindTmpl .arrive m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨l, tx, u, c, rl, sc, rfl⟩ := hm
  refine object_steps_inOrder hc.wf hc.max.1 hc.reads hc.guard
    hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
    (.inl ⟨l, tx, c, rl, sc, rfl⟩) (mb := l) (act := .arrive c tx) (fun _ _ h => by cases h)
    fun l' => ?_
  by_cases h : l' = l
  · subst h
    simp [objectAction, snoc_get_new]
  · simp [objectAction, snoc_get_new, h, Ne.symm h]

theorem tensorLoad_steps (hm : KindTmpl .tensorLoad m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, s, u, rfl⟩ := hm
  exact .inl (Step.issue_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (e := ⟨t1.pc, .tensorIssue a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩ (.inl ⟨a, s, rfl⟩)
    (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem tensorStore_steps (hm : KindTmpl .tensorStore m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, s, u, rfl⟩ := hm
  exact .inl (Step.issue_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (e := ⟨t1.pc, .tensorStore a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩
    (.inr (.inl ⟨a, s, rfl⟩)) (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem mma_steps (hm : KindTmpl .mma m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨dc, s, acc, ms, u, rfl⟩ := hm
  exact .inl (Step.tc_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem commit_steps (hm : KindTmpl .commit m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨s, u, rfl⟩ := hm
  exact .inl (Step.tc_counted_extension_reads hc.max.1 hc.reads hp.1 hne hrel hrun hl
    (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (hc.snoc_wf rfl)
    (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

theorem cluster_steps (hm : KindTmpl .cluster m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨op, u, rfl⟩ := hm
  exact .inl (Step.cluster_counted_extension hc.max.1 hp.1 hne hrel (hc.snoc_wf rfl) hrun hl
    (o := some u) ⟨_, hout, rfl, rfl⟩)

theorem bar_steps' (hm : KindTmpl .bar m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨id, u, c, md, rfl⟩ := hm
  exact .inl (Step.barArrival_counted_extension hc.max.1 hp.1 (.inl hne) hrel (hc.snoc_wf rfl)
    hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩)

theorem tmem_steps (hm : KindTmpl .tmem m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨grp, act, u, rfl, -⟩ := hm
  exact .inl (Step.tccoll_counted_extension hc.max.1 hp.1 (.inl hne) hrel hrun hl (o := some u)
    ⟨_, hout, rfl, rfl⟩ rfl (hc.max.1.tmemPairResult.snoc_not_wr nofun)
    (hc.max.1.tcRead_snoc_tc fun _ _ _ h => by cases h) (hc.snoc_wf rfl))

theorem bulkWait_steps (hm : KindTmpl .bulkWait m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨mode, n, u, rfl⟩ := hm
  exact .inl (Step.BulkWait.bulk_wait_counted_extension hc.max.1 hp.1 hne hrel (hc.snoc_wf rfl)
    hrun hl (u := u) ⟨_, hout, rfl, rfl⟩)

theorem tcLoad_steps (hm : KindTmpl .tcLoad m) : Steps L K A mem0 Obl rank X o := by
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

theorem read_steps (hm : KindTmpl .read m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨a, k, rfl⟩ := hm
  exact .inl (Step.read_source_counted_extension hc.max.1 hp.1 hne hrel hrun hl hout
    (fun bs r h => hc.readWf g t1.pc a bs r h) hc.guard)

/-- A store, when the thread's last event is no allocation request of lane 0 of its warp. -/
theorem store_steps (hm : KindTmpl .store m)
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

theorem init_steps (hm : KindTmpl .init m) : Steps L K A mem0 Obl rank X o := by
  obtain ⟨l, c, u, rfl⟩ := hm
  refine object_steps_inOrder hc.wf hc.max.1 hc.reads hc.guard
    hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
    (.inr ⟨l, c, rfl⟩) (mb := l) (act := .init c) (fun _ _ h => by cases h) fun l' => ?_
  by_cases h : l' = l
  · subst h
    simp [objectAction, snoc_get_new]
  · simp [objectAction, snoc_get_new, h, Ne.symm h]

omit hrun hl hout in
/-- **A released pending thread followed to a state whose instruction needs no partner
performs it** (`NextKind.Rest`: not a poll, a warp collective, a register request or an
allocation); at a store, when its last event is no allocation request of lane 0. -/
theorem released_steps (hC : ∀ g < L.threads, (C g).Sound) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d))
    (hk : ∀ ins, K.code[(C g).pc d]? = some ins → (opKind ins.op).Rest = false)
    (hlast : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op = .store →
      ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → laneOf L g ≠ 0) :
    Steps L K A mem0 Obl rank X o := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  obtain ⟨t1, ins, -, -, -, hins, -⟩ := Frame.end_at hC hp.1 hrun hσ
  have hr := hk ins hins
  have hk' : ∀ ins', K.code[(C g).pc d]? = some ins' → opKind ins'.op = opKind ins.op := by
    intro ins' h'
    rw [hins] at h'
    cases h'
    rfl
  generalize hkd : opKind ins.op = k at hr hk'
  refine next_class hc hC hp hσ hne hrel hk' fun t t1 m hrun hl hout hm => ?_
  cases k
  case wait | warp | reg | alloc | other => simp [NextKind.Rest] at hr
  case cluster => exact cluster_steps hc hp hne hrel hrun hl hout hm
  case bar => exact bar_steps' hc hp hne hrel hrun hl hout hm
  case tmem => exact tmem_steps hc hp hne hrel hrun hl hout hm
  case init => exact init_steps hc hp hne hrel hrun hl hout hm
  case arrive => exact arrive_steps hc hp hne hrel hrun hl hout hm
  case tensorLoad => exact tensorLoad_steps hc hp hne hrel hrun hl hout hm
  case tensorStore => exact tensorStore_steps hc hp hne hrel hrun hl hout hm
  case mma => exact mma_steps hc hp hne hrel hrun hl hout hm
  case commit => exact commit_steps hc hp hne hrel hrun hl hout hm
  case bulkWait => exact bulkWait_steps hc hp hne hrel hrun hl hout hm
  case tcLoad => exact tcLoad_steps hc hp hne hrel hrun hl hout hm
  case read => exact read_steps hc hp hne hrel hrun hl hout hm
  case quiet => exact quiet_steps' hc hp hne hrel hrun hl hout hm
  case store => exact store_steps hc hp hne hrel hrun hl hout hm (hlast ins hins hkd)
  case exit => exact exit_steps hc hp hne hrel hrun hl hout hm

end
end PTX.Descent

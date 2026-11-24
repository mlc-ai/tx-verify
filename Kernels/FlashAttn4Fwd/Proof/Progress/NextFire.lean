-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressNext
public import Lemmas.Kernel.NextReads
public import Lemmas.Step.ReadSource

@[expose] public section

/-! # The next event of a released pending thread: plain events, reads and the exit

A pending thread of a safe execution has a run that ends in a state (`Frame.run_some`), and by
local steps its machine reaches a concrete state whose template is undefined behaviour or of the
kind of its site (`NextFacts.fire`, `next_fire`). A template of undefined behaviour is performed
(`Descent.ub_steps_inOrder`). The extensions keep the commit-order assumption's constraint, since
they perform no commit arrive-on (`asms_wfInOrder`, `Assumption.WfStep.quiet`).

* A fence or a bulk commit uses no mbarrier object, no Tensor Core and no memory
  (`quiet_next_steps`, through `Descent.quiet_steps_inOrder`, given the order of the conflicts
  at the bytes that are read).
* A store to shared memory without release semantics and the exit are outside the asynchronous
  instructions (`store_next_steps`, `exit_next_steps`, `Step.plain_counted_extension`); a store
  follows no allocation request of lane 0 of a recorded warp request (`NextFacts.alloc_next`:
  after its request, lane 0 is at the address store), so the allocator's result rule holds.
* The allocation's store of its address writes column 0, which every recorded allocation
  returns (`NextSafe.alloc_base`, `allocStore_next_steps`).
* A read of shared memory takes, at each byte, a source that no write it sees hides
  (`read_next_steps`, `Step.read_source_counted_extension`).

Beside the thread facts (`NextFacts`), the classes use three facts of the execution as a whole
(`NextSafe`): the conflicting accesses at the bytes that are read are ordered, every Tensor
Memory write leaves a 4-byte word, and every recorded allocation returns column 0. The root
proves them from the safety goal (`ProgressNextGlue.lean`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- **The facts of the execution as a whole that the classes of a released pending thread
use**: the conflicting accesses at the bytes that are read are ordered, every Tensor Memory write
leaves a 4-byte word in its cell, and every recorded allocation returns column 0. -/
structure NextSafe (L : Launch) (X : Execution) : Prop where
  /-- The conflicting accesses at the bytes that are read are ordered. -/
  reads : ReadsOrdered L X
  /-- Every Tensor Memory write leaves a 4-byte word in its cell. -/
  words : ∀ s cell v, TcMma.Wrote L asms X s cell v → v.bytes = 4
  /-- Every recorded allocation returns column 0. -/
  alloc_base : ∀ (i : EvId) (pc : Nat) (grp : CtaGroup) (dst : Option Loc) (n cta : Nat)
    (x : Tmem.Pair.Requests) (base : Nat),
    X.get i = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → x ∈ X.tmemHistory cta →
    x.own.event L 0 = i → x.action = .alloc n base → base = 0

/-- What the classes of a released pending thread use of a maximal execution. -/
structure NextCtx (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  max : Maximal L kernel asms mem0 X
  safe : ¬ Unsafe L kernel asms mem0 X
  facts : NextFacts L X
  whole : NextSafe L X
  guard : SyncGuarded L kernel X
  no_release : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  no_release_rmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false
  no_fence : ∀ e sem s, ¬ X.ThreadFence e sem s
  layout : TcMma.LayoutInjective X

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The step of a released pending thread. -/
abbrev ThreadSteps (L : Launch) (mem0 : Mem0) (X : Execution) (g : Nat) : Prop :=
  Sched.Steps (timed L) mem0 X (.thread g)

theorem NextCtx.noUb (hc : NextCtx L mem0 X) : ¬ HasUb X := fun h => hc.safe (.inl h)

/-- The event of lane 0 of a recorded warp request is made by lane 0 of its warp. -/
theorem laneOf_event_zero (hX : Consistent L kernel asms mem0 X) {cta : Nat}
    {x : Tmem.Pair.Requests} (hx : x ∈ X.tmemHistory cta) : laneOf L (x.own.event L 0).1 = 0 := by
  obtain ⟨-, hw, -⟩ := ((hX.tmemPair.1 cta).1 x hx).2.2
  simp only [laneOf, Tmem.Pair.WarpRequest.event, Fin.val_zero, Nat.add_zero]
  rw [show x.own.cta * L.block + x.own.warp * 32 = x.own.warp * 32 + L.block * x.own.cta by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show x.own.warp * 32 < L.block by omega),
    Nat.mul_mod_left]

/-- A thread at a state of a kind other than a warp collective has made an event: its machine
starts at the prologue's first shuffle. -/
theorem ne_nil_of_kind {g : Nat} {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d ≠ .warp) :
    X.tr g ≠ [] := by
  intro h0
  have h0' : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inl ⟨.shfl0⟩)) := by
    rw [h0]
    exact Frame.stateAt_zero
  rw [h0'] at hσ
  cases hσ
  exact hk rfl

/-- **The next event of a released pending thread**: its run ends in a state, from which local
steps reach a concrete state of its machine state whose template is undefined behaviour or of
its site's kind. -/
theorem next_fire (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) :
    ∃ t t1 m, Run kernel asms L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel asms L g) t t1 ∧ (code L g).AtD d t1 ∧
      out kernel asms L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl (nextKind d) m) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  obtain ⟨t1, m, hl, hat, hout, hm⟩ := hc.facts.fire hp.1 hσ hrun
  exact ⟨t, t1, m, hrun, hl, hat, hout, hm⟩

/-- An extension by one appended event keeps the assumptions' constraints. -/
theorem snoc_wf (hX : Consistent L kernel asms mem0 X) {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} : ∀ a ∈ asms, a.wf L mem0 (X.snoc g e r) :=
  asms_wfInOrder _ _ hX le_snoc (Execution.notifiedInOrder_of_eq rfl)

/-- **A released pending thread at a site of kind `k`** (not a warp collective) steps when it
steps at every template of kind `k` its machine reaches by local steps; a template of undefined
behaviour is performed (`Descent.ub_steps_inOrder`). -/
theorem next_class (hc : NextCtx L mem0 X) {g : Nat} {o : Descent.Obligation}
    (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) {k : NextKind}
    (hk : nextKind d = k) (hkw : k ≠ .warp) (hrel : Step.Released L X g)
    (h : Consistent L kernel asms mem0 X → X.tr g ≠ [] → ∀ t t1 m,
      Run kernel asms L g {} (X.tr g) (some t) → Relation.ReflTransGen (Tau kernel asms L g) t t1 →
      out kernel asms L g t1 = .ev m → KindTmpl k m → Sched.Steps (timed L) mem0 X o) :
    Sched.Steps (timed L) mem0 X o := by
  have hne := ne_nil_of_kind hσ (by rw [hk]; exact hkw)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | hm
  · exact Descent.ub_steps_inOrder asms_wfStep hc.max.1 hp.1 hne hrel hrun hl hout
  · exact h hc.max.1 hne t t1 m hrun hl hout hm

/-- **A released pending thread at its exit steps**: it exits. -/
theorem exit_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .exit) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with rfl
  · exact .inl (Step.plain_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := none)
      (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
      (hX.tmemPairResult.snoc_not_wr nofun) (snoc_wf hX))

/-- **A released pending thread at a fence or a bulk commit steps.** -/
theorem quiet_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .quiet) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  have hX := hc.max.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  have hq := fun {m : Tmpl} {k : Kind} {u : TState} (hout : out kernel asms L g t1 = .ev m)
      (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
      (hk : (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ (∃ q r, k = .clcQuery q r) ∨
        k = .bulkCommit) =>
    Descent.quiet_steps_inOrder (Obl := Descent.Obl L) (rank := Sched.rank (timed L))
      (o := .thread g)
      asms_wfStep hX hc.whole.reads hc.guard hc.no_release hc.no_release_rmw hc.no_fence hp.1
      (.inl hne) hrel hrun hl hout hf hk
  rcases hm with ⟨f, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact Descent.ub_steps_inOrder asms_wfStep hX hp.1 hne hrel hrun hl hout
  · exact hq hout ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
  · exact hq hout ⟨rfl, rfl⟩ (.inr (.inl rfl))
  · exact hq hout ⟨rfl, rfl⟩ (.inr (.inr (.inr rfl)))

/-- **A released pending thread at a store to shared memory steps.** -/
theorem store_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .store) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨a, bs, u, rfl, hr⟩
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
  exact .inl (Step.plain_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
    (e := ⟨t1.pc, .wr a bs⟩) ⟨_, hout, rfl, rfl⟩ hr (by simp [Kind.isTma, hr])
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    hres (snoc_wf hX))

/-- **A released pending thread at the allocation's address store steps**: it writes column 0,
the column every recorded allocation returns. -/
theorem allocStore_next_steps (hc : NextCtx L mem0 X) {g : Nat} {o : Descent.Obligation}
    (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .allocStore) (hrel : Step.Released L X g) :
    Sched.Steps (timed L) mem0 X o := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨dst, u, rfl⟩
  let e : Event := ⟨t1.pc, .wr { loc := dst, size := 4 }
    (Value.bits 32 (BitVec.ofNat 64 0)).toBytes⟩
  have hres : Tmem.Pair.ResultOk L (X.snoc g e (fun _ => none)) := by
    apply hX.tmemPairResult.snoc
    intro pc a bs he _ pc' grp dst' n hget cta x base hx hwi hwa
    simp only [e, Event.mk.injEq, Kind.wr.injEq] at he
    obtain ⟨-, -, rfl⟩ := he
    rw [hc.whole.alloc_base _ pc' grp dst' n cta x base hget hx hwi hwa]
  exact .inl (Step.plain_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
    (e := e) ⟨_, hout, 0, by decide, rfl, rfl⟩ rfl (by simp [e, Kind.isTma])
    (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
    hres (snoc_wf hX))

/-- **A released pending thread at a read of shared memory steps.** -/
theorem read_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .read) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨a, k, rfl⟩
  · exact .inl (Step.read_source_counted_extension hX hp.1 hne hrel hrun hl hout
      (fun _ _ _ => snoc_wf hX) hc.guard)

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress

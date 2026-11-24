-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Static

@[expose] public section

/-!
# A released pending thread performs its next event

The kind of a released pending thread's next event (`nextKind`) picks its class. A pending thread
of a safe execution has a run that ends in a state (`Frame.run_some`), and by local steps its
machine reaches a concrete state whose template is undefined behaviour or of the kind of its site
(`fire`, `next_fire`). A template of undefined behaviour is performed (`ub_ext`). The extensions
keep the commit-order assumption's constraint, since they perform no commit arrive-on
(`asms_wfStep`, `Assumption.WfStep.quiet`); a read keeps the read-only input assumption's
constraint by its own step (`read_wf`).

* A fence or a bulk commit uses no mbarrier object, no Tensor Core and no memory (`quiet`).
* A store without release semantics and the exit are outside the asynchronous instructions
  (`store`, `exit`); a store follows no allocation request of lane 0 of a recorded warp request
  (`NextFacts.alloc_next`: after its request, lane 0 is at the address store), so the allocator's
  result rule holds.
* The allocation's store of its address writes column 0, which every recorded allocation returns
  (`NextSafe.alloc_base`).
* A read takes, at each byte, a source that no write it sees hides (`read`).
* An mbarrier initialization or arrival carries its checked record (`init`, `arrive`); a tensor
  copy issue, an MMA and a commit are issued by one thread (`tensorLoad`, `mma`, `commit`); a
  Tensor Memory load returns in each slot the value the last write of its cell left, a word
  (`tcLoad`), its wait, a Tensor Memory store and its wait, a named barrier, a paired Tensor
  Memory operation are warp-collective events appended as they are (`tcStore`, `bar`, `tmem`).

Beside the thread facts (`NextFacts`), the classes use three facts of the execution as a whole
(`NextSafe`): the conflicting accesses at the bytes that are read are ordered, every Tensor Memory
write leaves a 4-byte word, and every recorded allocation returns column 0. The register request
(`reg`) and the mbarrier polls and warp collectives are classes of their own
(`Assembly.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 100000

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The thread layer's facts about the next event**: a thread whose last event is an allocation
request is at the allocation's address store, or is not lane 0 of its warp (only lane 0 stores the
address, and the other lanes continue at the named barrier after it). -/
structure NextFacts (Q : Params) (L : Launch) (X : Execution) : Prop where
  alloc_next : ∀ {g pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat} {s : TSt},
    g < L.threads →
    X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ →
    St Q L X g (X.tr g).length = some (some s) → nextKind s = .allocStore ∨ laneOf L g ≠ 0

/-- **The facts of the execution as a whole that the classes of a released pending thread use**:
the conflicting accesses at the bytes that are read are ordered, every Tensor Memory write leaves a
4-byte word in its cell, and every recorded allocation returns column 0. -/
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
structure NextCtx (Q : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  max : Maximal L kernel asms mem0 X
  safe : ¬ Unsafe L kernel asms mem0 X
  sound : ∀ g < L.threads, (threadCode L g Q).Sound
  facts : NextFacts Q L X
  whole : NextSafe L X
  guard : SyncGuarded L kernel X
  layout : TcMma.LayoutInjective X
  /-- The next read of a followed thread at a site of the read-only input assumption reads bytes
  that no write covers (`Interface.ReadFresh`). -/
  fresh : ReadFresh Q L X

theorem NextCtx.noUb (hc : NextCtx Q L mem0 X) : ¬ HasUb X := fun h => hc.safe (.inl h)

/-- No thread is canceled and every thread counts as launched: the kernel issues no cancellation
request. -/
theorem launched (hX : Consistent L kernel asms mem0 X) (h : Nat) : Step.Launched L X h :=
  fun ⟨_, _, _, _, hi⟩ => (no_clc hX hi).elim

/-- A thread without events is at the first state of its machine, a named barrier or the
allocation. -/
theorem init_kind (L : Launch) (g : Nat) (Q : Params) :
    nextKind (threadCode L g Q).init = .bar ∨ nextKind (threadCode L g Q).init = .tmem := by
  by_cases hd : g % L.block < 128
  · have h1 : (threadCode L g Q).init = .d (.dstart (DStart.D.start L g)) := by
      simp only [threadCode, hd, ↓reduceIte]
    rw [h1]
    by_cases h32 : g % L.block < 32
    · right
      simp only [DStart.D.start, h32, ↓reduceIte]
      decide +kernel
    · left
      simp only [DStart.D.start, h32, ↓reduceIte]
      decide +kernel
  · have h1 : (threadCode L g Q).init = .w (.worker (Worker.D.start (Worker.startPro Q))) := by
      simp only [threadCode, hd, ↓reduceIte]
    rw [h1]
    left
    simp only [nextKind, TSt.pc, WComp.pc, TSt.sub, WComp.sub, Worker.D.start]
    decide +kernel

/-- A thread at a state of a kind other than a named barrier or a paired Tensor Memory operation
has made an event. -/
theorem ne_nil_of_kind {g : Nat} {s : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some s)) (hk : nextKind s ≠ .bar)
    (hk' : nextKind s ≠ .tmem) : X.tr g ≠ [] := by
  intro h0
  have h0' : St Q L X g (X.tr g).length = some (some (threadCode L g Q).init) := by
    rw [h0]
    exact Frame.stateAt_zero
  rw [h0'] at hσ
  obtain rfl := Option.some.inj (Option.some.inj hσ)
  rcases init_kind L g Q with h | h
  · exact hk h
  · exact hk' h

/-- An extension by one appended event keeps the assumptions' constraints. -/
theorem snoc_wf (hX : Consistent L kernel asms mem0 X) {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (h : e.kind.readsMem = false := by rfl) :
    ∀ a ∈ asms, a.wf L mem0 (X.snoc g e r) :=
  asms_wfStep.quiet hX le_snoc rfl (Execution.noNewRead_snoc h)

/-- **The next event of a released pending thread**: its run ends in a state, from which local
steps reach a concrete state of its machine state whose template is undefined behaviour or of its
site's kind. -/
theorem next_fire (hc : NextCtx Q L mem0 X) {g : Nat} (hp : Frame.Pending L X g) {s : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some s)) :
    ∃ t t1 m, Run kernel asms L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel asms L g) t t1 ∧ (threadCode L g Q).AtD s t1 ∧
      out kernel asms L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl (nextKind s) m) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  obtain ⟨t1, m, hl, hat, hout, hm⟩ := fire hc.sound hp.1 hσ hrun
  exact ⟨t, t1, m, hrun, hl, hat, hout, hm⟩

/-- **A released thread whose machine reaches undefined behaviour performs it.** -/
theorem ub_ext (hX : Consistent L kernel asms mem0 X) {h : Nat} (hh : h < L.threads)
    (hrel : Step.Released L X h) {t t1 : TState}
    (hrun : Run kernel asms L h {} (X.tr h) (some t))
    (hl : Relation.ReflTransGen (Tau kernel asms L h) t t1) {f : Fault}
    (hout : out kernel asms L h t1 = .ev (.ub f)) :
    ∃ Y, Consistent L kernel asms mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  Step.plain_counted_extension hX hh (.inr (launched hX h)) hrel hrun hl (o := none)
    ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl (hX.tmemPairResult.snoc_not_wr nofun)
    (snoc_wf hX)

/-- **A released pending thread whose template is undefined behaviour steps.** -/
theorem ub_steps (hc : NextCtx Q L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) {t t1 : TState}
    (hrun : Run kernel asms L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau kernel asms L g) t t1) {f : Fault}
    (hout : out kernel asms L g t1 = .ev (.ub f)) {o : Descent.Obligation} :
    Sched.Steps (timed T Q L) mem0 X o :=
  .inl (ub_ext hc.max.1 hp.1 hrel hrun hl hout)

/-- **A released pending thread at its exit steps**: it exits. -/
theorem exit_next_steps (hc : NextCtx Q L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .exit) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | rfl
  · exact ub_steps hc hp hrel hrun hl hout
  · exact .inl (Step.plain_counted_extension hX hp.1 (.inr (launched hX g)) hrel hrun hl (o := none)
      (e := ⟨t1.pc, .exit⟩) ⟨_, hout, rfl, rfl⟩ trivial rfl
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl
      (hX.tmemPairResult.snoc_not_wr nofun) (snoc_wf hX))

/-- **A released pending thread at a fence or a bulk commit steps.** -/
theorem quiet_next_steps (hc : NextCtx Q L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hk : nextKind s = .quiet) (hrel : Step.Released L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  have hq := fun {m : Tmpl} {k : Kind} {u : TState} (hout : out kernel asms L g t1 = .ev m)
      (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
      (hk : (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ (∃ q r, k = .clcQuery q r) ∨
        k = .bulkCommit) =>
    Descent.quiet_steps_inOrder (Obl := Descent.Obl L) (rank := Sched.rank (timed T Q L))
      (o := .thread g)
      asms_wfStep hX hc.whole.reads hc.guard (fun _ _ _ _ => no_release hX)
      (no_release_rmw hX) (no_threadFence hX) hp.1 (.inr (launched hX g)) hrel hrun hl hout hf hk
  rcases hm with ⟨f, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact ub_steps hc hp hrel hrun hl hout
  · exact hq hout ⟨rfl, rfl⟩ (.inl ⟨_, _, rfl⟩)
  · exact hq hout ⟨rfl, rfl⟩ (.inr (.inl rfl))
  · exact hq hout ⟨rfl, rfl⟩ (.inr (.inr (.inr rfl)))

end

end PTX.Kernels.InklingRelDecode.Proof.Progress

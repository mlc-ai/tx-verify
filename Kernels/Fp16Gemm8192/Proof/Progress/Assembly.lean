-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.AssemblySites
public import Kernels.Fp16Gemm8192.Proof.Progress.DrainWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.BulkWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.StoreWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.AccWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.ClcWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.Async
public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterLast
public import Kernels.Fp16Gemm8192.Proof.Progress.BarBlocked
public import Kernels.Fp16Gemm8192.Proof.Progress.RegWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.TmemWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.AllocPublish
public import Kernels.Fp16Gemm8192.Proof.Progress.NextObject
public import Kernels.Fp16Gemm8192.Proof.Progress.NextTc
public import Kernels.Fp16Gemm8192.Proof.Progress.NextIssue
public import Kernels.Fp16Gemm8192.Proof.Progress.NextRead
public import Kernels.Fp16Gemm8192.Proof.Progress.TcLoad
public import Kernels.Fp16Gemm8192.Proof.Progress.WarpWaitsStep
public import Lemmas.Flow.EndSite
public import Lemmas.Kernel.Unreleased

@[expose] public section

/-! # The progress assembly: every open obligation steps

Every open obligation of a maximal execution steps (`obl_steps`), so every maximal execution is
complete (`progress_of_classes`, through `Descent.progress_of_steps`).

A pending thread splits on its last event.

* Not released (`Step.Released` fails): its last event blocks and is not ready
  (`unreleased_cases`). An unrecorded cluster operation (`cluster_last_steps`), a register request
  some lane of the warp has not matched (`reg_wait_steps`), a paired Tensor Memory operation that
  cannot return yet (`tmem_wait_steps`), an unreleased named barrier arrival (`bar_wait_steps`), a
  Tensor Memory load or wait some lane of the warp has not reached (`tc_data_steps`), or a
  bulk-group wait whose stores are open (`bulk_unready_steps`). After an allocation completes,
  a lane waiting for the address can advance its warp's leader through the result store
  (`allocation_publication`).
* Released, machine stopped: the thread performs its undefined behaviour (`Descent.dead_steps`).
* Released, machine at a state: the kind of its next event (`nextKind`) picks the class. The
  mbarrier waits (loader empty, MMA full, both accumulator waits, CLC response, acknowledgement)
  poll (`Descent.mbar_wait_steps` through the class theorems; the loader's tail drain among them);
  the cluster, named barrier, register and Tensor Memory sites perform their operation
  (`*_next_steps`); a plain event, the exit, an mbarrier initialization or arrival, an MMA, a
  commit, a copy issue, a cancellation request and a read, a Tensor Memory load and its wait are
  performed (`NextPlain.lean`, `NextObject.lean`, `NextTc.lean`, `NextIssue.lean`, `NextRead.lean`,
  `TcLoad.lean`); a warp collective by `warp_steps` (`NextSteps L mem0 .warp`).

The asynchronous obligations: CLC notifications, linear copies, arrive-ons and commits drain
(`clc_steps`, `bulk_steps`, `arriveOn_steps`, `commit_steps`); the paired Tensor Memory
obligations pass to a pending thread (`tmem_steps`); an issued tensor store completes once its
staging bytes have visible sources (`store_obl_steps`); MMAs and tensor copies by
`ClassFacts.mmaObl` and `tensorObl`.

The per-execution facts the classes use are `ClassFacts`, instantiated at the top of the
tree (`Proof/ProgressFacts.lean`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow MBarrier Classical

noncomputable section

/-- The per-execution facts and blocker exports the proved classes use. -/
structure ClassFacts (L : Launch) (mem0 : Mem0) : Prop where
  /-- No consistent execution is unsafe. -/
  safe : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ Unsafe L kernel Prod mem0 Y
  thread : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y
  /-- Synchronization is guarded (`SyncGuarded`). -/
  guard : ∀ Y, Consistent L kernel Prod mem0 Y → SyncGuarded L kernel Y
  agree : ∀ Y, Consistent L kernel Prod mem0 Y → AllResponsesAgree L Y
  clusterAll : ∀ Y, Consistent L kernel Prod mem0 Y → ClusterExitAll L Y
  /-- The accumulator ring's values. -/
  words : ∀ Y, Consistent L kernel Prod mem0 Y → TmemWords L Y
  loader : LoaderEmptyFacts L mem0
  drain : DrainWaitFacts L mem0
  store : StoreFacts L mem0
  /-- An issued MMA that has not completed. -/
  mmaObl : ∀ X, Maximal L kernel Prod mem0 X → Descent.Obl L X .mma →
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X .mma
  /-- An issued tensor copy that has not notified. -/
  tensorObl : ∀ X, Maximal L kernel Prod mem0 X → Descent.Obl L X .tensor →
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X .tensor
  mmaFull : MmaFullFacts L mem0
  acc : AccWaitFacts L mem0
  consAcc : ConsAccBlocked L mem0
  clc : ClcWaitFacts L mem0
  /-- A consumer at its CLC response wait finds its CTA's response barrier initialized. -/
  consClcInit : ∀ Y g (c : Consumer.D), Consistent L kernel Prod mem0 Y → g < L.threads →
    Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.cons c))) → c.site = .clcWait →
    ∃ pc, Y.get (g / L.block * L.block, (⟨.clc, 0, true⟩ : Bar).initIndex) =
      some ⟨pc, .mbInit (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (⟨.clc, 0, true⟩ : Bar).count⟩
  /-- The machine does not stop after a cluster operation, a named barrier arrival or a
  bulk-group wait. -/
  live : ∀ Y g, Consistent L kernel Prod mem0 Y → g < L.threads → 0 < (Y.tr g).length →
    ((∃ pc op, Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .cluster op⟩) ∨
      (∃ pc id cnt, Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .bar id cnt⟩) ∨
      ∃ pc m n, Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .bulkWait m n⟩) →
    Frame.stateAt (code L) Y g (Y.tr g).length ≠ none

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The failing part of a release.** A thread whose last event is not released has a blocking
last event that is not ready (`Descent.unreleased_cases`): a cluster operation, a register request,
a paired Tensor Memory operation that cannot return yet, a named barrier arrival, a Tensor Memory
load or wait, or a bulk-group wait. The kernel has no `bar.arrive` and no `cp.async` group wait. -/
theorem unreleased_cases {g : Nat} (hX : Consistent L kernel Prod mem0 X)
    (h : ¬ Step.Released L X g) :
    (∃ pc op, X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩ ∧
      ¬ Ready L X (g, (X.tr g).length - 1)) ∨
    RegWait L X g ∨ TmemWait L X g ∨
    (∃ pc id cnt, X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt⟩) ∨
    (∃ e, X.get (g, (X.tr g).length - 1) = some e ∧ isTcData e = true) ∨
    (∃ pc m n, X.get (g, (X.tr g).length - 1) = some ⟨pc, .bulkWait m n⟩ ∧
      ¬ Ready L X (g, (X.tr g).length - 1)) := by
  obtain ⟨pc, k, hq, hk, hnr⟩ := Descent.unreleased_cases h
  cases k with
  | cluster op => exact .inl ⟨pc, op, hq, hnr⟩
  | setMaxReg inc n inst => exact .inr (.inl ⟨pc, inc, n, inst, hq, hnr⟩)
  | bar id cnt mode =>
    cases mode with
    | sync => exact .inr (.inr (.inr (.inl ⟨pc, id, cnt, hq⟩)))
    | arrive => exact (hX.noBarArrive Fact.out _ pc id cnt hq).elim
  | bulkWait m n => exact .inr (.inr (.inr (.inr (.inr ⟨pc, m, n, hq, hnr⟩))))
  | asyncWait n => exact (no_asyncWait hX hq).elim
  | tc t =>
    cases t with
    | resource group dst action => exact .inr (.inr (.inl (not_ready_tmem hq hnr)))
    | ld a vals shape => exact .inr (.inr (.inr (.inr (.inl ⟨_, hq, rfl⟩))))
    | st a vals shape => exact .inr (.inr (.inr (.inr (.inl ⟨_, hq, rfl⟩))))
    | waitLd => exact .inr (.inr (.inr (.inr (.inl ⟨_, hq, rfl⟩))))
    | waitSt => exact .inr (.inr (.inr (.inr (.inl ⟨_, hq, rfl⟩))))
    | _ => simp [Kind.resume, TcKind.resume] at hk
  | _ => simp [Kind.resume] at hk

/-- A checked mbarrier with an initialization of a valid count has a state after its history. -/
theorem init_state (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {b : Bar}
    {cta pc : Nat}
    (hinit : X.get (cta * L.block, b.initIndex) = some ⟨pc, .mbInit (b.loc L cta) b.count⟩) :
    ∃ before, stateBefore (X.objects (b.loc L cta)) (X.objects (b.loc L cta)).length =
      some before := by
  obtain ⟨i0, r, hr, -, hra, -, -⟩ := init_record_of_actual_get hX hinit
  refine stateBefore_length_some (hX.tma.2.2.1 _).1 (objects_noInval hX ht _)
      (List.mem_of_getElem? hr) hra ?_
  rcases b with ⟨ring, s, full⟩
  cases ring <;> cases full <;> simp only [Bar.count] <;> decide

/-- The CTA of a thread is below the grid. -/
theorem cta_lt (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) : g / L.block < L.grid := by
  have hb : 0 < L.block := by have := hpre.block; omega
  exact (Nat.div_lt_iff_lt_mul hb).mpr hg

/-- **A role at its CLC response wait steps** (`clc_wait_steps`): its time is at least the block
of its successful response polls plus six, and its CTA's response barrier is initialized. -/
theorem clc_class_steps (hC : ClassFacts L mem0) (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hd : d.AtClcWait) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have ht := hC.thread X hX
  have hub := noUb_of_safe (hC.safe X hX)
  have hub' : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩ := fun k pc f h => hub ⟨(g, k), pc, f, h⟩
  have hgrid := cta_lt hpre hg
  rcases d with p | r
  · exact hd.elim
  have hne := trace_ne_nil_of_role hσ
  have hinit : ∃ pc, X.get (g / L.block * L.block, (⟨.clc, 0, true⟩ : Bar).initIndex) =
      some ⟨pc, .mbInit (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (⟨.clc, 0, true⟩ : Bar).count⟩ :=
        by
    cases r with
    | cons c => exact hC.consClcInit X g c hX hg hσ hd
    | _ =>
      refine ht.ring_init_exists hg ?_ (le_refl _) hσ (by simp [Bar.Valid, Ring.slots]) hgrid rfl
      have := ht.role_warp hg (le_refl _) hσ
      simp only [roleWarp] at this
      omega
  obtain ⟨pc, hget⟩ := hinit
  obtain ⟨before, hstate⟩ := init_state hX ht hget
  refine clc_wait_steps hC.clc hmax hp hrel hne hσ hd ?_ hstate
  cases r with
  | loader l =>
    have hs : l.site = .clcWait := hd
    have hK := ht.loader_clc_count hg hub' hσ hs
    rw [threadTime_of hσ (by simp [ThreadD.exitOff, Loader.exitOff, hs])]
    simp only [ThreadD.vtime, Loader.vtime, hs, hK, Nat.add_sub_cancel]
    unfold blockAt
    omega
  | mma m =>
    have hs : m.site = .clcWait := hd
    have hD := ht.mma_clc_count hg hub' hσ hs
    rw [threadTime_of hσ (by simp [ThreadD.exitOff, Mma.exitOff, hs])]
    simp only [ThreadD.vtime, Mma.vtime, hs, hD, Nat.mul_div_cancel_left _ (by decide : 0 < 128)]
    unfold blockAt
    omega
  | sched s =>
    have hs : s.site = .clcWait := hd
    rw [threadTime_of hσ (by simp [ThreadD.exitOff, Scheduler.exitOff, hs])]
    simp only [ThreadD.vtime, Scheduler.vtime, hs, schedCount]
    exact le_refl _
  | cons c =>
    have hs : c.site = .clcWait := hd
    have hT : consCount L g (X.tr g) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
      have := ht.cons_tiles hg hub' hσ
      simpa [Consumer.tileOpen, Consumer.holds, hs] using this
    rw [threadTime_of hσ (by simp [ThreadD.exitOff, Consumer.exitOff, hs])]
    simp only [ThreadD.vtime, Consumer.vtime, hs, hT]
    omega

/-- **The leader scheduler at its acknowledgement wait steps** (`ack_wait_steps`): it runs on
its cluster's leader CTA in warp 10, its time is the block of its successful acknowledgement
polls, and its CTA's acknowledgement barrier is initialized. -/
theorem ack_class_steps (hC : ClassFacts L mem0) (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) {s : Scheduler.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched s))))
    (hs : s.site = .ackWait) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have ht := hC.thread X hX
  have hub := noUb_of_safe (hC.safe X hX)
  have hub' : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩ := fun k pc f h => hub ⟨(g, k), pc, f, h⟩
  have hgrid := cta_lt hpre hg
  have hne := trace_ne_nil_of_role hσ
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  obtain ⟨-, -, -, -, hinv, -⟩ := Frame.end_at ht.sound hg hrun hσ
  have hlead : Loader.leader L g = true := hinv.2 (.inl hs)
  have hw : g % L.block / 32 = 10 := by
    have := ht.role_warp hg (le_refl _) hσ
    simpa [roleWarp] using this
  obtain ⟨pc, hget⟩ := ht.ring_init_exists (b := ⟨.clc, 0, false⟩) hg (by omega) (le_refl _) hσ
    (by simp [Bar.Valid, Ring.slots]) hgrid rfl
  obtain ⟨before, hstate⟩ := init_state hX ht hget
  refine ack_wait_steps hC.clc hmax hp hrel hne (by simpa [Loader.leader] using hlead) hw
    (pcw := s.site.pc) (par := s.ap) (fun t hr ok => ?_) ?_ hstate
  · obtain ⟨t1, u, sc, h1, h2, -⟩ := ht.sched_ack_poll hg hσ hs hr ok
    exact ⟨t1, u, sc, h1, h2⟩
  · rw [threadTime_of hσ (by simp [ThreadD.exitOff, Scheduler.exitOff, hs]),
      ht.sched_ack_count hg hub' hσ hs]
    simp [ThreadD.vtime, Scheduler.vtime, hs, schedCount]

/-- **A released pending thread steps**, by the kind of its next event. -/
theorem released_steps (hC : ClassFacts L mem0) (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have ht := hC.thread X hX
  have hsafe := hC.safe X hX
  have hub := noUb_of_safe hsafe
  cases hσ : Frame.stateAt (code L) X g (X.tr g).length with
  | none => exact Descent.dead_steps prod_wfFree hmax hub ht.sound hp hσ hrel
  | some σ =>
    cases σ with
    | none => exact absurd hσ (ht.tracked g _ hg)
    | some d =>
      cases hk : nextKind d with
      | emptyWait =>
        obtain ⟨l, b, rfl, hs⟩ := nextKind_emptyWait hk
        exact loader_empty_steps hC.loader hpre hmax hp hσ hs hrel
      | fullWait =>
        obtain ⟨m, s, rfl, hs⟩ := nextKind_fullWait hk
        exact mma_full_steps hpre hC.mmaFull hmax hp hσ hs hrel
      | mmaAccWait =>
        obtain ⟨m, rfl, hs⟩ := nextKind_mmaAccWait hk
        exact mma_acc_steps hpre hub hmax ht hC.acc hp hσ hs hrel
      | consAccWait =>
        obtain ⟨c, rfl, hs⟩ := nextKind_consAccWait hk
        exact cons_acc_steps hub hmax ht hC.consAcc hp hσ hs hrel
      | clcWait => exact clc_class_steps hC hpre hmax hp hrel hσ (nextKind_clcWait hk)
      | ackWait =>
        obtain ⟨s, rfl, hs⟩ := nextKind_ackWait hk
        exact ack_class_steps hC hpre hmax hp hrel hσ hs
      | cluster => exact cluster_next_steps ht hub hmax hp hσ (nextKind_cluster hk) hrel
      | bar =>
        obtain ⟨c, rfl, hs⟩ := nextKind_bar hk
        exact bar_next_steps ht hub hmax hp hσ hs hrel
      | reg => exact reg_next_steps ht hmax hub hp hσ (nextKind_reg hk) hrel
      | tmem => exact tmem_next_steps ht hmax hub hp hσ (nextKind_tmem hk) hrel
      | warp => exact warp_steps hpre hC.thread hC.safe X g d hmax hp hσ hk hrel
      | drainWait =>
        obtain ⟨l, i, rfl, hs⟩ := nextKind_drainWait hk
        exact loader_drain_steps hC.drain hpre hmax hp hσ hs hrel
      | arrive => exact arrive_next_steps hpre ht (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | init => exact init_next_steps hpre ht (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | tensorLoad => exact tensorLoad_next_steps hpre ht (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | tensorStore => exact tensorStore_next_steps hpre ht (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | mma => exact mma_next_steps hpre ht (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | commit => exact commit_next_steps hpre ht (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | clcIssue => exact clcIssue_next_steps hpre ht (hC.guard X hX) hC.safe hmax hp hσ hk hrel
      | bulkWait =>
        obtain ⟨c, rfl, hs⟩ := nextKind_bulkWait hk
        exact bulk_next_steps ht hub hmax hp hσ hs hrel
      | tcLoad =>
        exact tc_load_next_steps ht (hC.words X hX) (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | read => exact read_next_steps ht (hC.guard X hX) hub hmax hp hσ hk hrel
      | plain => exact plain_next_steps hpre ht (hC.guard X hX) hsafe hmax hp hσ hk hrel
      | exit => exact exit_next_steps ht hub hmax hp hσ hk hrel

/-- **A pending thread steps**: by the failing part of its release, or by its next event. -/
theorem thread_steps (hC : ClassFacts L mem0) (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have ht := hC.thread X hX
  have hsafe := hC.safe X hX
  have hub := noUb_of_safe hsafe
  by_cases hrel : Step.Released L X g
  · exact released_steps hC hpre hmax hp hrel
  rcases unreleased_cases hX hrel with
    ⟨pc, op, hlast, hnr⟩ | hw | hw | ⟨pc, id, cnt, hlast⟩ | ⟨e, hlast, hd⟩ | ⟨pc, m, n, hlast, hnr⟩
  · cases hσ : Frame.stateAt (code L) X g (X.tr g).length with
    | none =>
      have hl : 0 < (X.tr g).length := by
        have := len_of_get hlast
        simp only at this
        omega
      exact absurd hσ (hC.live X g hX hg hl (.inl ⟨pc, op, hlast⟩))
    | some σ =>
      cases σ with
      | none => exact absurd hσ (ht.tracked g _ hg)
      | some dg => exact cluster_last_steps hpre ht hub hmax hp hσ hlast hnr
  · exact reg_wait_steps hpre ht hsafe hmax hp hw
  · by_cases hret : Tmem.Pair.ReturnReady L X (g, (X.tr g).length - 1)
    · obtain ⟨pc, group, dst, action, he, hn⟩ := hw
      cases action with
      | alloc n =>
        rcases allocation_publication hpre ht hX hub he hret with
          published | ⟨_, _, _, hp', hr', hstate⟩
        · exact (hn (Tmem.Pair.ReturnReady.ready hX.tmemPair he hret
            (fun _ _ _ => published))).elim
        · exact plain_next_steps hpre ht (hC.guard X hX) hsafe hmax hp' hstate rfl hr'
      | dealloc base n =>
        exact (hn (Tmem.Pair.ReturnReady.ready hX.tmemPair he hret
          (fun _ h _ => by cases h))).elim
      | relinquish =>
        exact (hn (Tmem.Pair.ReturnReady.ready hX.tmemPair he hret
          (fun _ h _ => by cases h))).elim
    · exact tmem_wait_steps hpre ht hsafe hmax hw hret
  · -- the arrival was a consumer's, on a barrier of 128 threads
    have hl : 0 < (X.tr g).length := by
      have := len_of_get hlast
      simp only at this
      omega
    obtain ⟨d0, hd0⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub hlast
    obtain ⟨c0, rfl⟩ := ht.bar_role hg hlast hd0 rfl
    have hcnt : cnt = some 128 := by
      rcases (ht.cons_out hg hlast hd0).2.2.2.2.1 id cnt rfl with
        ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> exact h
    subst hcnt
    have hlast' : (X.tr g)[(X.tr g).length - 1]? = some ⟨pc, .bar id (some 128)⟩ := hlast
    have hsucc := Frame.stateAt_succ (C := code L) hlast'
    rw [Nat.sub_add_cancel hl, hd0] at hsucc
    cases hσ : Frame.stateAt (code L) X g (X.tr g).length with
    | none => exact absurd hσ (hC.live X g hX hg hl (.inr (.inl ⟨pc, id, some 128, hlast⟩)))
    | some σ =>
      cases σ with
      | none => exact absurd hσ (ht.tracked g _ hg)
      | some dg =>
        rw [hσ] at hsucc
        have hn : (Consumer.next L g c0 ⟨pc, .bar id (some 128)⟩).map
            (Option.map (Sum.inr ∘ Prologue.Role.cons)) = some (some dg) := hsucc.symm
        rcases hcn : Consumer.next L g c0 ⟨pc, .bar id (some 128)⟩ with _ | _ | c
        · rw [hcn] at hn
          cases hn
        · rw [hcn] at hn
          cases hn
        · rw [hcn] at hn
          simp only [Option.map_some, Option.some.injEq, Function.comp_apply] at hn
          subst hn
          exact bar_wait_steps hpre ht hub hmax (hC.agree X hX)
            (hC.clusterAll X hX) hp hσ hlast hrel
  · exact tc_data_steps ht (hC.words X hX) hsafe hmax (hC.agree X hX) (hC.clusterAll X hX) hp
      hlast hd hrel
  · have hl : 0 < (X.tr g).length := by
      have := len_of_get hlast
      simp only at this
      omega
    exact bulk_unready_steps ht hub hmax hp hlast hnr
      (hC.live X g hX hg hl (.inr (.inr ⟨pc, m, n, hlast⟩)))

/-- **Every open obligation steps.** -/
theorem obl_steps (hC : ClassFacts L mem0) (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {o : Descent.Obligation} (ho : Descent.Obl L X o) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X o := by
  have hX := hmax.1
  have ht := hC.thread X hX
  have hsafe := hC.safe X hX
  have hub := noUb_of_safe hsafe
  cases o with
  | thread g => exact thread_steps hC hpre hmax ho
  | bulk => exact bulk_steps hmax ht hub ho
  | arriveOn => exact arriveOn_steps hmax ho
  | mma => exact hC.mmaObl X hmax ho
  | clc => exact clc_steps hmax ho
  | tensor => exact hC.tensorObl X hmax ho
  | store => exact store_obl_steps hC.store hmax (hC.guard X hmax.1) ho
  | commit => exact commit_steps hmax ho
  | tmem => exact tmem_steps hpre ht hsafe hmax ho

/-- **Progress from the classes.** Given the per-execution facts of the classes, every maximal
execution is complete. -/
theorem progress_of_classes (hC : ClassFacts L mem0)
    (hpre : Pre P L mem0) : ProgressGoal kernel Prod L mem0 :=
  Descent.progress_of_steps (Descent.Obl L) (rank L)
    (fun _ _ hn => Descent.cover hn)
    fun _ _ hmax ho => obl_steps hC hpre hmax ho

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress

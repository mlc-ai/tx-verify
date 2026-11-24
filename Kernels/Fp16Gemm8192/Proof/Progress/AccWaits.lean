-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.MmaFull

@[expose] public section

/-! # Progress at the accumulator waits

The two accumulator wait classes, each stepped by the mbarrier wait step `Descent.mbar_wait_steps`:

* an MMA leader at its accumulator-empty wait (`Mma.Site.accWait`) polls its warp's buffer
  `w % 2` on the leader CTA's empty barrier with its parity `ap` (`mma_acc_poll`);
* a consumer at its accumulator-full wait (`Consumer.Site.accWait`) polls its CTA's full barrier
  of its accumulator with its phase `ap` (`cons_acc_poll`).

A successful poll is a counted extension. A failed poll is blocked. The MMA blocker is a consumer
of the cluster that the accumulator witness names (`AccEmptyWitness`, a per-execution fact of
`AccWaitFacts`), a thread outside its exit stage whose time is below the MMA thread's. The consumer
blocker is a premise of the class, `ConsAccBlocked`, stated as the obligation of smaller rank that
the protocol layer must give (an undelivered commit or an MMA leader that has not committed the
tile); it is not proven here. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow MBarrier AsyncCopy

noncomputable section

/-- The accumulator-empty barrier of buffer `w % 2` in the leader CTA's warps: the one an MMA
thread of warp `w` polls, in thread `g`'s CTA. -/
abbrev mmaAccLoc (L : Launch) (g w : Nat) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + 8 * (w % 2) + 88⟩

/-- The accumulator-full barrier a consumer thread `g` polls: its CTA's, of its warp group. -/
abbrev consAccLoc (L : Launch) (g : Nat) : Loc :=
  Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩

/-- **The blocker of a consumer at its accumulator-full wait** (a premise, not proven here). In a
maximal execution where a consumer thread `g` stopped at a failed poll of its accumulator's full
barrier, whose phase has the poll's parity, some open obligation ranks below the thread's time,
`blockAt T + 4200` with `T` its successful accumulator polls. -/
def ConsAccBlocked (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ (Y : Execution) (g : Nat) (c : Consumer.D) (pc : Nat) (sc : MbarScope)
    (before : MBarrier.State),
    Maximal L kernel Prod mem0 Y → g < L.threads →
    Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.cons c))) → c.site = .accWait →
    (Y.tr g).getLast? = some ⟨pc, .wait (consAccLoc L g) c.ap false true sc⟩ →
    stateBefore (Y.objects (consAccLoc L g)) (Y.objects (consAccLoc L g)).length = some before →
    before.phase % 2 = c.ap % 2 →
    ∃ o', Descent.Obl L Y o' ∧ rank L Y o' < blockAt (consCount L g (Y.tr g)) + 4200

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The thread's state after a trace that is not empty, for a consumer. -/
theorem trace_ne_nil_of_cons {g : Nat} {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c)))) : X.tr g ≠
      [] := by
  intro h
  simp only [Frame.stateAt, h, List.length_nil, List.take_zero] at hσ
  cases hσ

/-- The per-execution facts the accumulator classes use. The MMA leaders' accumulator witness
(`witness`, the statement `AccEmptyWitness`) is proven in the protocol layer (`accEmptyWitness`)
from the MMA leaders' working claims (`mma_working_claims`, a consequence of the thread facts). The
consumers' accumulator-full barrier initialization is the thread fact `ThreadFacts.cons_acc_init`.
-/
structure AccWaitFacts (L : Launch) (mem0 : Mem0) : Prop where
  ub : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ HasUb Y
  thread : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y
  witness : ∀ Y, Consistent L kernel Prod mem0 Y → AccEmptyWitness L Y

/-- **Progress at an MMA leader's accumulator-empty wait.** A pending MMA thread at its
accumulator-empty wait, whose last event is released, extends a maximal execution or passes to an
obligation of smaller rank: the consumer that the accumulator witness of its failed poll names,
whose time is below the thread's rank `blockAt (D / 128) + 32` with `D` its commits. -/
theorem mma_acc_steps (hpre : Pre P L mem0) (hub : ¬ HasUb X) (hmax : Maximal L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hF : AccWaitFacts L mem0) {g : Nat} (hp : Frame.Pending L X g)
    {mm : Mma.D} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm))))
    (hs : mm.site = .accWait) (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0
      (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := trace_ne_nil_of_mma hσ
  have hblock := hpre.block
  have hgrid : g / L.block < L.grid := by
    have : g < L.grid * L.block := hg
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  have hw8 : 8 ≤ g % L.block / 32 := by
    have := ht.role_warp hg (le_refl _) hσ
    simp only [roleWarp] at this
    omega
  -- the barrier is initialized, so it has a state
  have hv : (⟨.acc, mm.w % 2, false⟩ : Bar).Valid := by
    simp only [Bar.Valid, Ring.slots]
    exact Nat.mod_lt _ (by decide)
  obtain ⟨ipc, hinit⟩ := ht.ring_init_exists (b := ⟨.acc, mm.w % 2, false⟩) hg hw8 (le_refl _) hσ
    hv hgrid rfl
  have hloc : Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩ = mmaAccLoc L g mm.w := by
    simp only [Bar.loc, Bar.off, mmaAccLoc]
    congr 1
    omega
  rw [hloc] at hinit
  obtain ⟨i0, r, hr, -, hra, -, -⟩ := init_record_of_actual_get hX hinit
  obtain ⟨before, hstate⟩ := stateBefore_length_some (hX.tma.2.2.1 (mmaAccLoc L g mm.w)).1
      (objects_noInval hX ht (mmaAccLoc L g mm.w))
    (List.mem_of_getElem? hr) hra (by simp only [Bar.count]; decide)
  -- the rank of the thread
  have hrank : rank L X (.thread g) = blockAt (mmaCount L g (X.tr g) / 128) + 32 := by
    rw [rank_released hrel, threadTime_of hσ (by simp [ThreadD.exitOff, Mma.exitOff, hs])]
    simp [ThreadD.vtime, Mma.vtime, hs]
  refine Descent.mbar_wait_steps prod_wfFree hub hmax hp hrel hne
    (fun t hrun ok => ht.mma_acc_poll hg hσ hs hrun ok) hstate fun sc hafter hready hYmax => ?_
  set Y := Step.failedPoll X g mm.site.pc mm.ap (mmaAccLoc L g mm.w) true sc before with hY
  have htrY : Y.tr g = X.tr g ++ [⟨mm.site.pc, .wait (mmaAccLoc L g mm.w) mm.ap false true sc⟩] :=
    by
    rw [hY, Step.failedPoll_tr]; simp
  have hσY : Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.mma mm))) := by
    simp only [Frame.stateAt, List.take_length]
    rw [htrY]
    exact hafter
  have hlastY : (Y.tr g).getLast? = some ⟨mm.site.pc,
      .wait (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) mm.ap false true sc⟩ := by
    rw [htrY, hloc]; simp
  have hstateY : stateBefore (Y.objects (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩))
      (Y.objects (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩)).length = some before := by
    rw [hloc, hY, Step.failedPoll_objects]
    simp only [ite_true, List.length_append, List.length_singleton]
    simp [stateBefore, Step.failedRecord]
  have hYX : Consistent L kernel Prod mem0 Y := hYmax.1
  have hYt : ThreadFacts L Y := hF.thread Y hYX
  have hubY : ¬ HasUb Y := hF.ub Y hYX
  -- the MMA thread is on its cluster's leader CTA (it is not in the common exit)
  have hlead : g / L.block % 2 = 0 := by
    have hl : mm.site = .exitArrive ∨ mm.site = .exitWait ∨ mm.site = .exit ∨
        g / L.block % 2 = 0 := ht.mma_lead hg hσ
    rcases hl with h1 | h1 | h1 | h1
    · simp [hs] at h1
    · simp [hs] at h1
    · simp [hs] at h1
    · exact h1
  -- the accumulator witness of the failed poll: a consumer `kc` of the buffer in the cluster, in
  -- the buffer's warp group, which has arrived as many times as the phase, outside its exit stage
  obtain ⟨hTY, kc, hkc, hsame, hwg, harr, hnx, hexo⟩ :=
    hF.witness Y hYX g mm mm.site.pc sc before hg hlead hσY hs hlastY hstateY hready
  -- the MMA thread's accumulator polls at `Y`: its phase plus one is its task count
  have hKB : before.phase + 1 = mmaCount L g (Y.tr g) / 128 := by
    have hB := (hYt.mma_acc_count hg (fun k pc f hk => hubY ⟨(g, k), pc, f, hk⟩) hσY).2
    simp [hs] at hB
    omega
  have hK : mmaCount L g (Y.tr g) = mmaCount L g (X.tr g) := by
    rw [htrY]
    simp [mmaCount, List.countP_append, commitsTo]
  -- the consumer is not canceled: its cluster's MMA thread has a role state, so its trace is
  -- nonempty
  have hYget : Y.get (g, (X.tr g).length) =
      some ⟨mm.site.pc, .wait (mmaAccLoc L g mm.w) mm.ap false true sc⟩ := by
    change (Y.tr g)[(X.tr g).length]? = _
    rw [htrY]
    simp
  have hYσ : Frame.stateAt (code L) Y g (X.tr g).length = some (some (.inr (.mma mm))) := by
    have htk : (Y.tr g).take (X.tr g).length = X.tr g := by
      rw [htrY]
      exact List.take_left' rfl
    unfold Frame.stateAt
    rw [htk]
    simpa [Frame.stateAt] using hσ
  have hclus : L.clusterOfCta (kc / L.block) = L.clusterOfCta (g / L.block) := by
    rw [clusterOfCta_eq hpre, clusterOfCta_eq hpre]
    omega
  have hkne : Y.tr kc ≠ [] := hYt.cluster_started hg hYget hYσ hkc hclus
  have hpend : Frame.Pending L Y kc := ⟨hkc, fun hc => hkne hc.1, hnx⟩
  -- the consumer's time: a thread outside its exit stage ranks below `blockAt n + 32`, where `n`
  -- is the MMA leader's task count (`Consumer.vtime_lt_block`); prologue times are small
  have hv56 : ∀ s : Prologue.Site, Prologue.Site.vtime s ≤ 56 := by
    intro s
    cases s with
    | init i =>
      have hi := i.isLt
      show 4 + 2 * i.val ≤ 56
      omega
    | shfl => decide
    | elect => decide
    | alloc => decide
    | allocWrite => decide
    | warpBar => decide
    | fence => decide
    | fenceInit => decide
    | arrive => decide
    | wait => decide
    | setMaxReg => decide
    | roleElect => decide
  have hblockpos : ∀ n, 64 ≤ blockAt n := fun n => by
    unfold blockAt
    exact Nat.le_add_right _ _
  have hloc2 : Bar.loc L (2 * (kc / L.block / 2)) ⟨.acc, Consumer.tidOf L kc / 32 / 4, false⟩ =
      Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩ := by
    have h1 : 2 * (kc / L.block / 2) = g / L.block := by omega
    have h2 : Consumer.tidOf L kc / 32 / 4 = mm.w % 2 := hwg
    rw [h1, h2]
  have hTT : threadTime L Y kc + 1 < blockAt (mmaCount L g (Y.tr g) / 128) + 32 := by
    have hb := hblockpos (mmaCount L g (Y.tr g) / 128)
    obtain ⟨σ, hσk⟩ : ∃ σ, Frame.stateAt (code L) Y kc (Y.tr kc).length = σ := ⟨_, rfl⟩
    cases σ with
    | none =>
      simp only [threadTime, hσk]
      omega
    | some σ' =>
      cases σ' with
      | none =>
        simp only [threadTime, hσk]
        omega
      | some d =>
        rw [threadTime_of hσk (hexo d hσk)]
        cases d with
        | inl p =>
          have hp56 := hv56 p.site
          simp only [ThreadD.vtime]
          omega
        | inr r =>
          have hrw := hYt.role_warp hkc (le_refl _) hσk
          cases r with
          | loader l =>
            simp only [roleWarp] at hrw
            exact absurd hrw (by omega)
          | mma m' =>
            simp only [roleWarp] at hrw
            exact absurd hrw.2 (by omega)
          | sched s =>
            simp only [roleWarp] at hrw
            exact absurd hrw (by omega)
          | cons c =>
            have hcc := hYt.cons_acc_count hkc hσk
            rw [hloc2, harr] at hcc
            have hv := Consumer.vtime_lt_block c before.phase (consCount L kc (Y.tr kc)) hcc
            rw [hKB] at hv
            simp only [ThreadD.vtime]
            exact hv
  refine ⟨.thread kc, hpend, ?_⟩
  have hr := rank_thread_le (L := L) (X := Y) (g := kc)
  rw [hrank, ← hK]
  omega

/-- **Progress at a consumer's accumulator-full wait.** A pending consumer thread at its
accumulator-full wait, whose last event is released, extends a maximal execution or passes to an
obligation of smaller rank (`ConsAccBlocked`). The barrier's initialization is the thread fact
`ThreadFacts.cons_acc_init`. -/
theorem cons_acc_steps (hub : ¬ HasUb X) (hmax : Maximal L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hblk : ConsAccBlocked L mem0)
    {g : Nat} (hp : Frame.Pending L X g)
    {c : Consumer.D} (hσ : Frame.stateAt (code L) X g (X.tr g).length =
      some (some (.inr (.cons c))))
    (hs : c.site = .accWait) (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0
      (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := trace_ne_nil_of_cons hσ
  obtain ⟨ipc, hget⟩ := ht.cons_acc_init hg hσ hs
  obtain ⟨i0, r, hr, -, hra, -, -⟩ := init_record_of_actual_get hX hget
  obtain ⟨before, hstate⟩ := stateBefore_length_some (hX.tma.2.2.1 (consAccLoc L g)).1
      (objects_noInval hX ht (consAccLoc L g))
    (List.mem_of_getElem? hr) hra (by simp only [Bar.count]; decide)
  -- the rank of the thread
  have hrank : rank L X (.thread g) = blockAt (consCount L g (X.tr g)) + 4200 := by
    rw [rank_released hrel, threadTime_of hσ (by simp [ThreadD.exitOff, Consumer.exitOff, hs])]
    simp [ThreadD.vtime, Consumer.vtime, hs]
  refine Descent.mbar_wait_steps prod_wfFree hub hmax hp hrel hne
    (fun t hrun ok => ht.cons_acc_poll hg hσ hs hrun ok) hstate fun sc hafter hready hYmax => ?_
  set Y := Step.failedPoll X g Consumer.Site.accWait.pc c.ap (consAccLoc L g) true sc before with hY
  have htrY : Y.tr g = X.tr g ++ [⟨Consumer.Site.accWait.pc,
      .wait (consAccLoc L g) c.ap false true sc⟩] := by
    rw [hY, Step.failedPoll_tr]; simp
  have hσY : Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.cons c))) := by
    simp only [Frame.stateAt, List.take_length]
    rw [htrY]
    exact hafter
  have hlastY : (Y.tr g).getLast? = some ⟨Consumer.Site.accWait.pc,
      .wait (consAccLoc L g) c.ap false true sc⟩ := by
    rw [htrY]; simp
  have hstateY : stateBefore (Y.objects (consAccLoc L g))
      (Y.objects (consAccLoc L g)).length = some before := by
    rw [hY, Step.failedPoll_objects]
    simp only [ite_true, List.length_append, List.length_singleton]
    simp [stateBefore, Step.failedRecord]
  obtain ⟨o', hobl, hlt⟩ := hblk Y g c Consumer.Site.accWait.pc sc before hYmax hg hσY hs hlastY
    hstateY hready
  have hK : consCount L g (Y.tr g) = consCount L g (X.tr g) := by
    rw [htrY]
    simp [consCount, Flow.okPolls, List.countP_append, okPoll, sourceWaitSuccess]
  refine ⟨o', hobl, ?_⟩
  rw [hrank, ← hK]
  exact hlt

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress

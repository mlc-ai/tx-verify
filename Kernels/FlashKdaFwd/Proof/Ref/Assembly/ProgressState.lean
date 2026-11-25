-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ProgressNums

@[expose] public section

/-!
# The progress contract at one followed state: tile index, ledgers, arrival bounds, polls

The fields of `Proof/Schedule/Contract.lean: RefProgress` that speak about ONE followed state
`d` of a thread `g` (the state of its machine before its `k`-th event) and counts over its
first `k` events, for the numbers `nums P L` of `ProgressNums.lean`. Each is proved by a case
split over the phase the state is in (`Stage.lean`), with the phase's own export.

**Words.** A *followed state* at position `k` is `At (code L) X g k d`. The *stage* of a
followed state is its phase with the phase's invariant (`Stage P L X g k d`). `NoUb X g k`: none
of the first `k` events of thread `g` is undefined behaviour; the invariants of the Store phase
and of the epilogue are stated under it. `bar0Of pc` is the number of `bar.sync 0` instructions
below instruction `pc`. A *class* of events is a Boolean predicate counted along a trace.

**The generic arguments** (no phase is named in them):

* `early_before`: before a state at an instruction up to 1402 every followed state is at an
  instruction up to 1402. (The count of a thread's `bar.sync 0` grows along its trace and is
  `bar0Of` of the state's instruction: 5 at most up to 1402, 6 at least after it.)
* `early_matrix`, `early_bar8`: so a thread at an instruction up to 1402 has made no matrix
  event and no named barrier (those are fired at sites after 1402 only).
* `late_pc`: from the exit of the startup phase on, every followed state is at instruction 387
  or later (a thread that left the startup phase is not in it again).
* `coll_late`: so the shuffles and elections of a thread past the startup phase are those of
  the startup's exit: all the collective positions of its warp.
* `count_mono`: a count over a longer prefix is not smaller; lower bounds on arrivals at the
  exit of a phase hold at every later position.

Everything is in the sub-namespace `Assembly.Progress`. The section hypothesis `hub` is "no
undefined-behaviour event of the thread" (`∀ k, NoUb X g k`): the final theorem
(`Progress.lean: refProgress`) has it from its hypothesis that the execution has no
undefined-behaviour event. The lemmas that do not need it say so (`omit hub`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Progress
open PTX PTX.Proof PTX.Flow PTX.Sched
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses loadLeader storeLeader bar0Pcs ctaTiles)
open PTX.Kernels.FlashKdaFwd.Proof.Progress (siteCls kindCls siteCls_kind matBefore
  matBefore_eq bar0Of bar8Of collOf collPcs roundOf pollerOf coll_pc matrix_pc_range collAll
  matrixSites_all)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Generic facts -/

/-- **A position beyond a thread's trace has the state and the events of the last position**:
a fact about a followed state and the events before it need only be proved up to the length of
the trace. -/
theorem clamp {k : Nat} {d : D} (hσ : At (code L) X g k d) :
    ∃ K, K ≤ (X.tr g).length ∧ At (code L) X g K d ∧ (X.tr g).take k = (X.tr g).take K := by
  rcases Nat.le_total k (X.tr g).length with hk | hk
  · exact ⟨k, hk, hσ, rfl⟩
  · refine ⟨(X.tr g).length, le_rfl, ?_, ?_⟩
    · rw [At, ← Frame.stateAt_of_le hk]
      exact hσ
    · rw [List.take_of_length_le hk, List.take_length]

/-- A count over a longer prefix of a trace is not smaller. -/
theorem count_mono (c : Event → Bool) (l : List Event) {j k : Nat} (h : j ≤ k) :
    (l.take j).countP c ≤ (l.take k).countP c :=
  (List.take_sublist_take_left h).countP_le

/-- More instructions below a later instruction. -/
theorem bar0Of_mono {p p' : Nat} (h : p ≤ p') : bar0Of p ≤ bar0Of p' :=
  (List.monotone_filter_right _ fun a ha => by
    simp only [decide_eq_true_eq] at ha ⊢
    omega).length_le

theorem bar0Of_1402 : bar0Of 1402 = 5 := by decide

theorem bar0Of_1403 : bar0Of 1403 = 6 := by decide

/-- A site of the class of the warp collectives is an election or a shuffle. -/
theorem coll_site {s : Site} (h : siteCls s = .coll) :
    (∃ j, s = .elect j) ∨ ∃ j, s = .shfl j := by
  cases s <;> first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩ | cases h

/-- A site of a kind that fires matrix events is of the class of the matrix events. -/
theorem cls_of_matrixKind {s : Site} (h : s.kind ∈ matrixKinds) : siteCls s = .matrix := by
  rw [siteCls_kind]
  simp only [matrixKinds, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> rfl

/-- A site of the kind of an election or a shuffle is of the class of the warp collectives. -/
theorem cls_of_collKind {s : Site} (h : s.kind ∈ [SiteKind.elect, SiteKind.shfl]) :
    siteCls s = .coll := by
  rw [siteCls_kind]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h <;> rw [h] <;> rfl

/-- A site of the class of the polls is an `mbarrier.try_wait`. -/
theorem poll_site {s : Site} (h : siteCls s = .poll) : ∃ j, s = .mbarWait j := by
  cases s <;> first | exact ⟨_, rfl⟩ | cases h

/-- The ten polls of the program: the one of the startup at instruction 384, the others in the
three tile loops. -/
theorem wait_pc_cases : ∀ j : Fin 10, (Site.mbarWait j).pc = 384 ∨
    (1402 < (Site.mbarWait j).pc ∧ (Site.mbarWait j).pc < 3113) := by decide

/-- The collective positions are at instructions up to 312. -/
theorem collAll_le : ∀ p ∈ collAll, p ≤ 312 := by decide

/-- **No matrix instruction lies below an instruction up to 2105**, and such an instruction is
no row write of an `stmatrix`: the consumer's count `matBefore` is 0 there. -/
theorem matBefore_early {s : Site} (h : s.pc ≤ 2105) : matBefore s = 0 := by
  rw [matBefore_eq (by omega)]
  have h1 : (Top.matrixSites.filter (fun e => e.1 < s.pc)) = [] := by
    refine List.filter_eq_nil_iff.mpr fun e he => ?_
    have := List.all_eq_true.mp matrixSites_all e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [decide_eq_true_eq]
    omega
  have h2 : s.kind ≠ .matrixStoreWr := by
    intro hk
    obtain ⟨j, row, rfl⟩ : ∃ j row, s = .matrixStoreWr j row := by
      cases s <;> first | exact ⟨_, _, rfl⟩ | cases hk
    have h3 := matrix_pc_range (s := .matrixStore j) rfl
    have h4 : (Site.matrixStoreWr j row).pc = (Site.matrixStore j).pc := rfl
    omega
  rw [h1, ite_eq_right h2]
  rfl

/-- The collectives below an instruction, in the terms of the startup phase's list. -/
theorem collOf_eq (w pc : Nat) :
    ((Startup.collList w).filter (· < pc)).length = collOf w pc := rfl

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) (hub : ∀ k, NoUb X g k)
include hpre hX hg hub

/-! ### The `bar.sync 0` count orders the phases -/

/-- **Field `bar0`** at a followed state up to the end of the trace. -/
theorem bar0_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = bar0Of d.site.pc :=
  (stage hpre hX hg hk hσ).bar0 (hub k)

/-- **Before a state at an instruction up to 1402 every followed state is at an instruction up
to 1402.** -/
theorem early_before {k i : Nat} {d di : D} (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k d) (hpc : d.site.pc ≤ 1402) (hi : i ≤ k)
    (hσi : At (code L) X g i di) : di.site.pc ≤ 1402 := by
  by_contra h
  have h1 := bar0_at hpre hX hg hub hk hσ
  have h2 := bar0_at hpre hX hg hub (le_trans hi hk) hσi
  have h3 := count_mono (Execution.isBarId 0) (X.tr g) hi
  have h4 : bar0Of d.site.pc ≤ bar0Of 1402 := bar0Of_mono hpc
  have h5 : bar0Of 1403 ≤ bar0Of di.site.pc := bar0Of_mono (by omega)
  rw [bar0Of_1402] at h4
  rw [bar0Of_1403] at h5
  omega

/-- **A thread at an instruction up to 1402 has made no matrix event.** -/
theorem early_matrix {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hpc : d.site.pc ≤ 1402) : ((X.tr g).take k).countP isMatrix = 0 :=
  count_zero_of_state (sounds hpre) hX firedOnly_isMatrix hσ (Nat.le_succ k)
    fun i di hik hdi => .inl fun hmem => by
      have hp := early_before hpre hX hg hub hk hσ hpc (Nat.le_of_lt hik) hdi
      have := matrix_pc_range (cls_of_matrixKind hmem)
      omega

/-- **A thread at an instruction up to 1402 has made no named barrier** (`bar.sync 8`): the
barriers up to 1402 are `bar.sync 0`. -/
theorem early_bar8 {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hpc : d.site.pc ≤ 1402) : ((X.tr g).take k).countP (Execution.isBarId 8) = 0 :=
  count_zero_of_state (sounds hpre) hX (firedOnly_isBarId 8) hσ (Nat.le_succ k)
    fun i di hik hdi => .inr fun e he => by
      by_cases hb : di.site.kind = .bar
      · obtain ⟨j, hj⟩ := site_of_bar hb
        have hp := early_before hpre hX hg hub hk hσ hpc (Nat.le_of_lt hik) hdi
        have hm : di.site.pc ∈ bar0Pcs := by
          rcases bar_pc j with h | h
          · rw [hj]
            exact h
          · rw [hj] at hp
            omega
        rw [isBarId_bar0 (sounds hpre) hX he hdi hm 8]
        rfl
      · exact not_class_of_kind (sounds hpre) hX (firedOnly_isBarId 8) he hdi (by simpa using hb)

omit hub in
/-- **From the exit of the startup phase on, every followed state is at instruction 387 or
later.** -/
theorem late_pc {j0 i : Nat} {s0 di : D} (past : StartupDone P L X g j0 s0) (hji : j0 ≤ i)
    (hi : i ≤ (X.tr g).length) (hσi : At (code L) X g i di) : 387 ≤ di.site.pc := by
  have hst := stage hpre hX hg hi hσi
  by_contra hlt
  exact (hst.of_pc_startup (by omega)).inv.not_left ⟨j0, hji, s0, past.state, past.out.1⟩

omit hub in
/-- **Field `coll` past the startup phase**: the thread's shuffles and elections are all the
collective positions of its warp. -/
theorem coll_late {j0 k : Nat} {s0 d : D} (past : StartupDone P L X g j0 s0) (hj : j0 ≤ k)
    (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d) :
    ((X.tr g).take k).countP isWarpColl = collOf (g % L.block / 32) d.site.pc := by
  have h1 : ((X.tr g).take k).countP isWarpColl = ((X.tr g).take j0).countP isWarpColl :=
    count_transport_of_state (sounds hpre) hX Compute.firedOnly_isWarpColl hj hσ
      (Nat.le_succ k) fun i di h1 h2 hdi => .inl fun hmem => by
        have hp := late_pc hpre hX hg past h1 (by omega) hdi
        have := collAll_le _ (coll_pc (cls_of_collKind hmem)).1
        omega
  have h0 : s0.site.pc = 387 := by
    rw [past.out.1.1.site]
    rfl
  have hd := late_pc hpre hX hg past hj hk hσ
  rw [h1, Startup.coll_startup (.inr past.out), collOf_eq, warp_eq hpre, h0,
    Compute.collOf_late (by omega), Compute.collOf_late (by omega)]

/-! ### The startup's exit behind a state of a later phase -/

omit hpre hX hg hub in
/-- **A followed state is in the startup phase, or the thread left the startup phase at or
before it** (with the history record of that exit). -/
theorem startup_or_done {k : Nat} {d : D} (hst : Stage P L X g k d) :
    Startup.InvE P X g k d ∨ ∃ j0 s0, StartupDone P L X g j0 s0 ∧ j0 ≤ k := by
  cases hst with
  | startup hI => exact .inl hI
  | conversion past hj hI => exact .inr ⟨_, _, past, hj⟩
  | carryLoad past hj hI =>
    obtain ⟨j1, s1, p1, hlen, -⟩ := past.entry
    exact .inr ⟨j1, s1, p1, by omega⟩
  | compute hr past hj hin hI =>
    obtain ⟨j2, s2, p2, hlen2, -⟩ := past.entry
    obtain ⟨j1, s1, p1, hlen, -⟩ := p2.entry
    exact .inr ⟨j1, s1, p1, by omega⟩
  | producer hr past hj hen hI =>
    obtain ⟨j2, s2, p2, hlen2, -⟩ := past.entry
    obtain ⟨j1, s1, p1, hlen, -⟩ := p2.entry
    exact .inr ⟨j1, s1, p1, by omega⟩
  | store hr past hj hin hI hW =>
    obtain ⟨j2, s2, p2, hlen2, -⟩ := past.entry
    obtain ⟨j1, s1, p1, hlen, -⟩ := p2.entry
    exact .inr ⟨j1, s1, p1, by omega⟩
  | epilogue past hj hW hI =>
    obtain ⟨j3, s3, p3, hj3, -⟩ := past.entry
    obtain ⟨j2, s2, p2, hlen2, -⟩ := p3.entry
    obtain ⟨j1, s1, p1, hlen, -⟩ := p2.entry
    exact .inr ⟨j1, s1, p1, by omega⟩

/-! ### The fields about the tile index and the ledgers -/

omit hub in
/-- **Field `coll`**: the shuffles and elections of a thread are the collective positions of
its warp below the state's instruction. -/
theorem coll_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d) :
    ((X.tr g).take k).countP isWarpColl = collOf (g % L.block / 32) d.site.pc := by
  rcases startup_or_done (stage hpre hX hg hk hσ) with hI | ⟨j0, s0, past, hj⟩
  · rw [Startup.coll_startup (.inl hI), collOf_eq, warp_eq hpre]
  · exact coll_late hpre hX hg past hj hk hσ

omit hub in
/-- **Field `collAt`**: a state at a shuffle or an election is at a collective position of the
thread's own warp. -/
theorem collAt_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hc : siteCls d.site = .coll) : d.site.pc ∈ collPcs (g % L.block / 32) := by
  have hp := collAll_le _ (coll_pc hc).1
  have hI := (stage hpre hX hg hk hσ).of_pc_startup (by omega)
  rw [warp_eq hpre]
  exact Startup.collAt_startup hI.inv (coll_site hc)

/-! ### From the instruction and the role to the phase's invariant -/

omit hpre hX hg hub in
/-- A followed state of a compute thread between the instructions 1402 and 3113 is a state of
the Compute phase. -/
theorem compute_inv {k : Nat} {d : D} (hst : Stage P L X g k d) (h1 : 1402 < d.site.pc)
    (h2 : d.site.pc < 3113) (hr : tid g < 128) :
    ∃ j0 s0, CarryLoadDone P L X g j0 s0 ∧ j0 ≤ k ∧ Compute.In P L X g j0 s0 ∧
      Compute.Inv P L X g j0 k d := by
  have hrange : 2105 < d.site.pc ∧ d.site.pc ≤ 2944 := by
    rcases hst.pc_cases with h | h | h | ⟨-, h⟩ | ⟨hr', h⟩ | ⟨hr', h⟩ | h
    · omega
    · omega
    · omega
    · omega
    · have := (warp_eq4_iff g).mp hr'
      omega
    · have := (warp_eq5_iff g).mp hr'
      omega
    · omega
  exact (hst.of_pc_compute hrange.1 hrange.2).2

omit hpre hX hg hub in
/-- A followed state of a thread of the load warp between the instructions 1402 and 3113 is a
state of the Producer phase. -/
theorem producer_inv {k : Nat} {d : D} (hst : Stage P L X g k d) (h1 : 1402 < d.site.pc)
    (h2 : d.site.pc < 3113) (hr : warp g = 4) :
    ∃ j0 s0, CarryLoadDone P L X g j0 s0 ∧ j0 ≤ k ∧ Producer.Entered P L X g j0 ∧
      Producer.Inv P L X g k d := by
  have h4 := (warp_eq4_iff g).mp hr
  have hrange : d.site.pc ≤ 2105 := by
    rcases hst.pc_cases with h | h | h | ⟨hr', h⟩ | ⟨-, h⟩ | ⟨hr', h⟩ | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · have := (warp_eq5_iff g).mp hr'
      omega
    · omega
  exact (hst.of_pc_producer h1 hrange).2

omit hpre hX hg hub in
/-- A followed state of a thread of the store warp between the instructions 1402 and 3113,
with no undefined-behaviour event before it, is a state of the Store phase. -/
theorem store_inv {k : Nat} {d : D} (hst : Stage P L X g k d) (h1 : 1402 < d.site.pc)
    (h2 : d.site.pc < 3113) (hr : warp g = 5) (hu : NoUb X g k) : Store.Inv P X g k d := by
  have h5 := (warp_eq5_iff g).mp hr
  have hrange : 2944 < d.site.pc ∧ d.site.pc ≤ 3112 := by
    rcases hst.pc_cases with h | h | h | ⟨hr', h⟩ | ⟨hr', h⟩ | ⟨-, h⟩ | h
    · omega
    · omega
    · omega
    · omega
    · have := (warp_eq4_iff g).mp hr'
      omega
    · omega
    · omega
  obtain ⟨-, _, _, -, -, -, hI, -⟩ := hst.of_pc_store hrange.1 hrange.2
  exact hI hu

omit hpre hX hg hub in
/-- A followed state from instruction 3113 on, with no undefined-behaviour event before it, is
a state of the epilogue: the history record of the thread's tile loop, and the invariant. -/
theorem epi_inv {k : Nat} {d : D} (hst : Stage P L X g k d) (h : 3113 ≤ d.site.pc)
    (hu : NoUb X g k) :
    ∃ j0 s0, TileDone P L X g j0 s0 ∧ j0 ≤ k ∧ Epilogue.InvW P X g j0 k d ∧
      Epilogue.Inv P L X g j0 k d := by
  obtain ⟨j0, s0, past, hj, hW, hI⟩ := hst.of_pc_epilogue h (.inl hu)
  exact ⟨j0, s0, past, hj, hW, hI hu⟩

omit hpre hX hg hub in
/-- The exit of the Compute phase behind the epilogue of a compute thread. -/
theorem compute_out {j : Nat} {s : D} (past : TileDone P L X g j s) (hr : tid g < 128) :
    ∃ j0, Compute.Out P L X g j0 j s := by
  obtain ⟨j0, s0, -, -, h⟩ := past.entry
  rcases h with ⟨-, -, ho, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · exact ⟨j0, ho⟩
  · have := (warp_eq4_iff g).mp hw
    omega
  · have := (warp_eq5_iff g).mp hw
    omega

omit hpre hX hg hub in
/-- The exit of the Producer phase behind the epilogue of a thread of the load warp. -/
theorem producer_out {j : Nat} {s : D} (past : TileDone P L X g j s) (hr : warp g = 4) :
    Producer.Out P L X g j s := by
  have h4 := (warp_eq4_iff g).mp hr
  obtain ⟨j0, s0, -, -, h⟩ := past.entry
  rcases h with ⟨hc, -⟩ | ⟨-, -, ho, -⟩ | ⟨hw, -⟩
  · omega
  · exact ho
  · have := (warp_eq5_iff g).mp hw
    omega

omit hpre hX hg hub in
/-- The exit of the Store phase behind the epilogue of a thread of the store warp. -/
theorem store_out {j : Nat} {s : D} (past : TileDone P L X g j s) (hr : warp g = 5) :
    Store.Out P X g j s := by
  have h5 := (warp_eq5_iff g).mp hr
  obtain ⟨j0, s0, -, -, h⟩ := past.entry
  rcases h with ⟨hc, -⟩ | ⟨hw, -⟩ | ⟨-, -, ho, -⟩
  · omega
  · have := (warp_eq4_iff g).mp hw
    omega
  · exact ho

omit hpre hX hg hub in
/-- **A class of events that no event of the epilogue belongs to keeps its count from the
entry of the epilogue.** -/
theorem epi_count {j0 k : Nat} {d : D} (hI : Epilogue.Inv P L X g j0 k d) {c : Event → Bool}
    (hc : Epilogue.Quiet P L g c) :
    ((X.tr g).take k).countP c = ((X.tr g).take j0).countP c := by
  obtain ⟨pos, -, -, -, -, -, hq⟩ := hI
  exact hq c hc

omit hpre hX hg hub in
theorem bar8Of_low {pc T : Nat} (h : pc ≤ 2913) : bar8Of pc T = T := by
  unfold bar8Of
  rw [ite_eq_right (by omega)]

omit hpre hX hg hub in
theorem bar8Of_high {pc T : Nat} (h : 2944 < pc) : bar8Of pc T = T := by
  unfold bar8Of
  rw [ite_eq_right (by omega)]

omit hpre hX hg hub in
theorem matBefore_late {s : Site} (h : 3113 ≤ s.pc) : matBefore s = 0 := by
  unfold matBefore
  rw [ite_eq_left h]

/-! ### The tile index -/

/-- **Field `tile_le`**: the tile index is at most the tile count. -/
theorem tile_le_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k d) : tileNum P L g d ≤ ctaTiles P (g / L.block) := by
  have hst := stage hpre hX hg hk hσ
  rcases Nat.lt_or_ge 1402 d.site.pc with h1 | h1
  · rcases Nat.lt_or_ge d.site.pc 3113 with h2 | h2
    · rw [tiles_eq hpre]
      rcases role_cases g with hr | hr | hr
      · rw [tileNum_compute h1 h2 hr]
        exact Compute.tileOf_le P g d
      · obtain ⟨j0, s0, -, -, -, hI⟩ := producer_inv hst h1 h2 hr
        rw [tileNum_producer h1 h2 hr]
        exact (Producer.tile_producer hpre hI).1
      · rw [tileNum_store h1 h2 hr]
        exact (Store.tileIdx_store hpre (L := L) (store_inv hst h1 h2 hr (hub k))).1
    · rw [tileNum_end h2]
  · rw [tileNum_start h1]
    exact Nat.zero_le _

omit hub in
/-- **Field `tile_matrix`**: a thread at a matrix event is a compute thread inside a tile. -/
theorem tile_matrix_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hm : siteCls d.site = .matrix) :
    g % L.block < 128 ∧ tileNum P L g d < ctaTiles P (g / L.block) := by
  have hst := stage hpre hX hg hk hσ
  have hp := matrix_pc_range hm
  obtain ⟨hr, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute (by omega) (by omega)
  rw [tileNum_compute (by omega) (by omega) hr, tiles_eq hpre]
  exact Compute.tile_matrix_compute hpre hI hm

/-! ### The ledgers of a compute thread -/

/-- **Field `bar8`**: the named barriers of a compute thread. -/
theorem bar8_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hr : tid g < 128) :
    ((X.tr g).take k).countP (Execution.isBarId 8) = bar8Of d.site.pc (tileNum P L g d) := by
  have hst := stage hpre hX hg hk hσ
  rcases Nat.lt_or_ge 1402 d.site.pc with h1 | h1
  · rcases Nat.lt_or_ge d.site.pc 3113 with h2 | h2
    · obtain ⟨j0, s0, -, -, -, hI⟩ := compute_inv hst h1 h2 hr
      rw [tileNum_compute h1 h2 hr]
      exact Compute.bar8_compute hpre hI
    · obtain ⟨j0, s0, past, -, -, hI⟩ := epi_inv hst h2 (hub k)
      obtain ⟨j1, ho⟩ := compute_out past hr
      rw [epi_count hI (Epilogue.quiet_isBarId (by decide)), Compute.bar8_out ho,
        Compute.tileOf_exit ho.1, ho.1.site, Compute.exit_pc, tileNum_end h2, tiles_eq hpre,
        bar8Of_high (by omega), bar8Of_high (by omega)]
  · rw [early_bar8 hpre hX hg hub hk hσ h1, tileNum_start h1, bar8Of_low (by omega)]

/-- **Field `matrix`**: the matrix events of a compute thread. -/
theorem matrix_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hr : tid g < 128) :
    ((X.tr g).take k).countP isMatrix = 182 * tileNum P L g d + matBefore d.site := by
  have hst := stage hpre hX hg hk hσ
  rcases Nat.lt_or_ge 1402 d.site.pc with h1 | h1
  · rcases Nat.lt_or_ge d.site.pc 3113 with h2 | h2
    · obtain ⟨j0, s0, -, -, -, hI⟩ := compute_inv hst h1 h2 hr
      rw [tileNum_compute h1 h2 hr]
      exact Compute.matrix_compute hpre hI
    · obtain ⟨j0, s0, past, -, -, hI⟩ := epi_inv hst h2 (hub k)
      obtain ⟨j1, ho⟩ := compute_out past hr
      rw [epi_count hI Epilogue.quiet_isMatrix, Compute.matrix_out ho,
        Compute.tileOf_exit ho.1, ho.1.site, Compute.matBefore_exit, tileNum_end h2,
        tiles_eq hpre, matBefore_late h2]
  · rw [early_matrix hpre hX hg hub hk hσ h1, tileNum_start h1, matBefore_early (by omega)]

/-- **Field `arrLoadEmpty`**: a compute thread has arrived on the "empty" mbarrier of an input
stage once per earlier tile of that stage. -/
theorem arrLoadEmpty_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k d) (hr : tid g < 128) (st : Fin 3) :
    uses 3 (tileNum P L g d) st.val ≤
      arrivals ((Bar.loadEmpty st).loc L (g / L.block)) ((X.tr g).take k) := by
  have hst := stage hpre hX hg hk hσ
  rcases Nat.lt_or_ge 1402 d.site.pc with h1 | h1
  · rcases Nat.lt_or_ge d.site.pc 3113 with h2 | h2
    · obtain ⟨j0, s0, -, -, -, hI⟩ := compute_inv hst h1 h2 hr
      rw [tileNum_compute h1 h2 hr]
      exact Compute.arrLoadEmpty_compute hpre hI st
    · obtain ⟨j0, s0, past, hj, -, -⟩ := epi_inv hst h2 (hub k)
      obtain ⟨j1, ho⟩ := compute_out past hr
      have h := (Compute.arr_out ho).1 st
      rw [Compute.tileOf_exit ho.1] at h
      rw [tileNum_end h2, tiles_eq hpre]
      exact le_trans h (count_mono _ _ hj)
  · rw [tileNum_start h1, Protocol.uses_zero 3 st.val st.isLt]
    exact Nat.zero_le _

/-- **Field `arrStoreFull`**: a compute thread has arrived on the "full" mbarrier of an output
stage once per earlier tile of that stage. -/
theorem arrStoreFull_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k d) (hr : tid g < 128) (o : Fin 2) :
    uses 2 (tileNum P L g d) o.val ≤
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) := by
  have hst := stage hpre hX hg hk hσ
  rcases Nat.lt_or_ge 1402 d.site.pc with h1 | h1
  · rcases Nat.lt_or_ge d.site.pc 3113 with h2 | h2
    · obtain ⟨j0, s0, -, -, -, hI⟩ := compute_inv hst h1 h2 hr
      rw [tileNum_compute h1 h2 hr]
      exact Compute.arrStoreFull_compute hpre hI o
    · obtain ⟨j0, s0, past, hj, -, -⟩ := epi_inv hst h2 (hub k)
      obtain ⟨j1, ho⟩ := compute_out past hr
      have h := (Compute.arr_out ho).2 o
      rw [Compute.tileOf_exit ho.1] at h
      rw [tileNum_end h2, tiles_eq hpre]
      exact le_trans h (count_mono _ _ hj)
  · rw [tileNum_start h1, Protocol.uses_zero 2 o.val o.isLt]
    exact Nat.zero_le _

/-! ### The ledgers of the two leaders -/

omit hX hg hub in
/-- The load leader of a block has index 128 in its block: it is of the load warp. -/
theorem loadLeader_tid (hgl : g = loadLeader L (g / L.block)) : tid g = 128 := by
  have hb := hpre.block
  unfold tid
  rw [hgl]
  simp only [loadLeader, Protocol.thr, hb]
  omega

omit hX hg hub in
/-- The store leader of a block has index 160 in its block: it is of the store warp. -/
theorem storeLeader_tid (hgl : g = storeLeader L (g / L.block)) : tid g = 160 := by
  have hb := hpre.block
  unfold tid
  rw [hgl]
  simp only [storeLeader, Protocol.thr, hb]
  omega

/-- **Field `arrLoadFull`**: the load leader has made its arrival and issued its 70 loads for
every earlier tile of a load stage. -/
theorem arrLoadFull_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k d) (hgl : g = loadLeader L (g / L.block)) (st : Fin 3) :
    uses 3 (tileNum P L g d) st.val ≤
        arrivals ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take k) ∧
      70 * uses 3 (tileNum P L g d) st.val ≤
        ((X.tr g).take k).countP (issuesTo ((Bar.loadFull st).loc L (g / L.block))) := by
  have hst := stage hpre hX hg hk hσ
  have ht := loadLeader_tid hpre hgl
  have hr : warp g = 4 := (warp_eq4_iff g).mpr (by omega)
  rcases Nat.lt_or_ge 1402 d.site.pc with h1 | h1
  · rcases Nat.lt_or_ge d.site.pc 3113 with h2 | h2
    · obtain ⟨j0, s0, -, -, -, hI⟩ := producer_inv hst h1 h2 hr
      rw [tileNum_producer h1 h2 hr]
      exact (Producer.tile_producer hpre hI).2.2 st
    · obtain ⟨j0, s0, past, hj, -, -⟩ := epi_inv hst h2 (hub k)
      have ho := producer_out past hr
      obtain ⟨-, ha, hi⟩ := Producer.exit_counts ht ho.2 st
      rw [tileNum_end h2, tiles_eq hpre]
      exact ⟨le_trans (le_of_eq ha.symm) (count_mono _ _ hj),
        le_trans (le_of_eq hi.symm) (count_mono _ _ hj)⟩
  · rw [tileNum_start h1, Protocol.uses_zero 3 st.val st.isLt]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

omit hX hg hub in
/-- At the exit of the Store phase a thread of the store warp has arrived on the "empty"
mbarrier of an output stage once per tile of that stage (the leader of a nonempty sequence), or
its sequence has no tile or it is no leader and the bound is about the leader only. -/
theorem store_arr_out {k : Nat} {s : D} (ho : Store.Out P X g k s) (hl0 : lane g = 0)
    (o : Fin 2) :
    uses 2 (tiles (P.length (seqOf P g))) o.val ≤
      arrivals ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k) := by
  have hl := ho.2
  have ho2 := o.isLt
  rw [← Store.emptyBar_eq hpre g o]
  by_cases hlen : 1 ≤ P.length (seqOf P g)
  · simp only [Store.ledExit, hl0, hlen, and_self, ↓reduceIte] at hl
    have h0 : arrivals (Store.emptyBar P g 0) ((X.tr g).take k) =
        (tiles (P.length (seqOf P g)) + 1) / 2 := congrArg Store.Led.arrE0 hl
    have h1 : arrivals (Store.emptyBar P g 1) ((X.tr g).take k) =
        tiles (P.length (seqOf P g)) / 2 := congrArg Store.Led.arrE1 hl
    obtain ⟨v, hv⟩ := o
    obtain rfl | rfl : v = 0 ∨ v = 1 := by omega
    · simp only [uses, h0]
      omega
    · simp only [uses, h1]
      omega
  · have h0 : P.length (seqOf P g) = 0 := by omega
    rw [h0]
    simp only [uses, tiles]
    omega

/-- **Field `arrStoreEmpty`**: the store leader has arrived on the "empty" mbarrier of an output
stage once per earlier tile of that stage. -/
theorem arrStoreEmpty_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k d) (hgl : g = storeLeader L (g / L.block)) (o : Fin 2) :
    uses 2 (tileNum P L g d) o.val ≤
      arrivals ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k) := by
  have hst := stage hpre hX hg hk hσ
  have ht := storeLeader_tid hpre hgl
  have hr : warp g = 5 := (warp_eq5_iff g).mpr (by omega)
  have hl0 : lane g = 0 := by
    have := tid_eq g
    have := lane_lt g
    omega
  rcases Nat.lt_or_ge 1402 d.site.pc with h1 | h1
  · rcases Nat.lt_or_ge d.site.pc 3113 with h2 | h2
    · rw [tileNum_store h1 h2 hr]
      exact (Store.tileIdx_store hpre (store_inv hst h1 h2 hr (hub k))).2.2 o
    · obtain ⟨j0, s0, past, hj, -, -⟩ := epi_inv hst h2 (hub k)
      rw [tileNum_end h2, tiles_eq hpre]
      exact le_trans (store_arr_out hpre (store_out past hr) hl0 o) (count_mono _ _ hj)
  · rw [tileNum_start h1, Protocol.uses_zero 2 o.val o.isLt]
    exact Nat.zero_le _

omit hub in
/-- **Field `arrState`**: the load leader past its third `bar.sync 0` has arrived on the state
barrier and issued the 16 loads of the initial state. -/
theorem arrState_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hgl : g = loadLeader L (g / L.block)) (hpc : 379 < d.site.pc) :
    1 ≤ arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k) ∧
      16 ≤ ((X.tr g).take k).countP (issuesTo (Bar.state.loc L (g / L.block))) := by
  rcases startup_or_done (stage hpre hX hg hk hσ) with hI | ⟨j0, s0, past, hj⟩
  · exact Startup.arrState_startup hpre hX hg hσ (.inl hI.inv) hgl hpc
  · have h0 := Startup.arrState_startup hpre hX hg past.state (.inr past.out.1) hgl
      (by rw [past.out.1.1.site]; decide)
    exact ⟨le_trans h0.1 (count_mono _ _ hj), le_trans h0.2 (count_mono _ _ hj)⟩

/-! ### Polls -/

/-- **Field `poll`**: a poll state polls one mbarrier of the thread's block, of which the
thread is a poller; it has made at most one successful poll of it per earlier tile of the
mbarrier's stage; in the startup the mbarrier is the state barrier; and every wait event the
state fires is on that mbarrier, with the parity of the thread's successful polls of it plus the
mbarrier's offset. -/
theorem poll_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hp : siteCls d.site = .poll) :
    ∃ b : Bar, pollerOf L (g / L.block) b g ∧
      okPolls (b.loc L (g / L.block)) ((X.tr g).take k) ≤ roundOf b (tileNum P L g d) ∧
      (d.site.pc ≤ 1402 → b = .state) ∧
      ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
        (code L g).AtD d t → kernel.code[d.site.pc]? = some ins →
        Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
        ∀ l q ok acq sc, e.kind = .wait l q ok acq sc →
          l = b.loc L (g / L.block) ∧
            q % 2 = (okPolls l ((X.tr g).take k) + b.delta) % 2 := by
  have hst := stage hpre hX hg hk hσ
  obtain ⟨j, hj⟩ := poll_site hp
  have hpcs := wait_pc_cases j
  rw [← hj] at hpcs
  rcases hpcs with h384 | ⟨h1, h2⟩
  · have hI := hst.of_pc_startup (by omega)
    obtain ⟨h0, hfire⟩ := Startup.poll_startup hpre hg hI.inv hj
    refine ⟨.state, trivial, ?_, fun _ => rfl, ?_⟩
    · rw [h0]
      exact Nat.zero_le _
    · intro t ins e o hat hc hf l q ok acq sc hkind
      obtain ⟨rfl, rfl⟩ := hfire hat hc hf l q ok acq sc hkind
      refine ⟨rfl, ?_⟩
      rw [h0]
      rfl
  · rcases role_cases g with hr | hr | hr
    · obtain ⟨j0, s0, -, -, -, hI⟩ := compute_inv hst h1 h2 hr
      rw [tileNum_compute h1 h2 hr]
      exact Compute.poll_compute hpre hI hp
    · obtain ⟨j0, s0, -, -, -, hI⟩ := producer_inv hst h1 h2 hr
      obtain ⟨st, hlead, hcnt, hpc, hfire⟩ := Producer.poll_producer hpre hg hr hI ⟨j, hj⟩
      rw [tileNum_producer h1 h2 hr]
      refine ⟨.loadEmpty st, hlead, le_of_eq hcnt, fun h => absurd h (by omega), ?_⟩
      intro t ins e o hat hc hf l q ok acq sc hkind
      exact hfire hat hc hf l q ok acq sc hkind
    · have hI := store_inv hst h1 h2 hr (hub k)
      obtain ⟨t, -, ht, hlt, hlead, hpc, hcnt, hfire⟩ := Store.poll_store hpre hg hI hj
      rw [tileNum_store h1 h2 hr, ht]
      refine ⟨.storeFull (Protocol.stageOf t), hlead, le_of_eq hcnt,
        fun h => absurd h (by omega), ?_⟩
      intro tt ins e o hat hc hf l q ok acq sc hkind
      obtain ⟨hl, hq⟩ := hfire hat hc hf l q ok acq sc hkind
      exact ⟨hl, hq⟩

/-- **Field `pollStage`**: a wait event that a poll state fires on the "full" mbarrier of a
load stage or of a store stage is on the stage of the state's tile, and the tile index is below
the tile count. -/
theorem pollStage_at {k : Nat} {d : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k d)
    (hp : siteCls d.site = .poll) {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) (q : Nat)
    (ok acq : Bool) (sc : MbarScope) :
    (∀ s : Fin 3, e.kind = .wait ((Bar.loadFull s).loc L (g / L.block)) q ok acq sc →
        s.val = tileNum P L g d % 3 ∧ tileNum P L g d < ctaTiles P (g / L.block)) ∧
      (∀ s : Fin 2, e.kind = .wait ((Bar.storeFull s).loc L (g / L.block)) q ok acq sc →
        s.val = tileNum P L g d % 2 ∧ tileNum P L g d < ctaTiles P (g / L.block)) := by
  have hst := stage hpre hX hg hk hσ
  obtain ⟨j, hj⟩ := poll_site hp
  have hpcs := wait_pc_cases j
  rw [← hj] at hpcs
  rcases hpcs with h384 | ⟨h1, h2⟩
  · have hI := hst.of_pc_startup (by omega)
    obtain ⟨h0, hfire⟩ := Startup.poll_startup hpre hg hI.inv hj
    refine ⟨fun s hk' => ?_, fun s hk' => ?_⟩
    · have h := (hfire hat hc hf _ q ok acq sc hk').1
      cases (Bar.loc_inj h).1
    · have h := (hfire hat hc hf _ q ok acq sc hk').1
      cases (Bar.loc_inj h).1
  · rcases role_cases g with hr | hr | hr
    · obtain ⟨j0, s0, -, -, -, hI⟩ := compute_inv hst h1 h2 hr
      rw [tileNum_compute h1 h2 hr, tiles_eq hpre]
      exact Compute.pollStage_compute hpre hI hp hat hc hf q ok acq sc
    · obtain ⟨j0, s0, -, -, -, hI⟩ := producer_inv hst h1 h2 hr
      refine ⟨fun s hk' => ?_, fun s hk' => ?_⟩
      · exact absurd rfl
          ((Producer.pollStage_producer hpre hg hr hI ⟨j, hj⟩ hat hc hf hk').1 s)
      · exact absurd rfl
          ((Producer.pollStage_producer hpre hg hr hI ⟨j, hj⟩ hat hc hf hk').2 s)
    · have hI := store_inv hst h1 h2 hr (hub k)
      obtain ⟨tl, -, ht, hlt, hlead, hpc, hcnt, hfire⟩ := Store.poll_store hpre hg hI hj
      refine ⟨fun s hk' => ?_, fun s hk' => ?_⟩
      · have h := (hfire hat hc hf _ q ok acq sc hk').1
        cases (Bar.loc_inj h).1
      · have h := (hfire hat hc hf _ q ok acq sc hk').1
        obtain rfl : s = Protocol.stageOf tl := Bar.storeFull.inj (Bar.loc_inj h).1
        rw [tileNum_store h1 h2 hr, ht, tiles_eq hpre]
        exact ⟨rfl, hlt⟩

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Progress

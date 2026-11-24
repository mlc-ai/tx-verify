-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.PlainSafety
public import Lemmas.Kernel.Obligation
public import Lemmas.Step.Released

@[expose] public section

/-! # Executions whose asynchronous events are mbarriers, bulk copies and `tcgen05` instructions

The counterpart of `Execution.NoTma` (`Lemmas/Kernel/PlainSafety`, `Lemmas/Kernel/Descent`) for a
kernel that synchronizes through mbarrier objects and copies with `cp.async.bulk`. An event kind is
of the mbarrier/bulk class (`Kind.isMbarBulk`) unless it is a tensor copy or prefetch, a cluster
launch control request or query, a cluster barrier operation, a `tcgen05` instruction, a register
request, a warp collective (shuffle, warp barrier, election, warp matrix instruction) or a
`cp.async.mbarrier.arrive`. In an execution all of whose events are of this class
(`Execution.MbarBulk`), every branch of `Unsafe` that needs one of the excluded events is empty,
and `Execution.MbarBulk.not_unsafe` leaves the kernel the branches its own events decide:

* no undefined behaviour (`HasUb`) and no unallocated byte (`Unalloc`);
* conflicting accesses ordered at every byte (`ConflictsOrdered … fun _ => True`);
* CTA barriers matched (`BarMismatch`) and not faulting (`CtaBarFault`), and no aligned
  instruction diverging or left by an exit (`AlignedMismatch`);
* the mbarrier and linear-copy branch `TmaUnsafe`, the initialization of every mbarrier operand
  (`MbarUninit`) and no linear reduction without a value (`TensorStore.CopyReduceNoRule`);
* every poll a canonical spin or unused (`PollShapeUnsafe`);
* no assumption's undefined behaviour, and no warp-divergent guard;
* every shared-memory use in time (`SharedLifetimeUnsafe`).

For progress, the only obligations such an execution can leave open are its pending threads and
its linear copies (`Execution.MbarBulk.open_cases`), and without CTA barriers every thread is
released (`Execution.MbarBulk.released`).

The wider class `Execution.TcBulk` (`Kind.isTcBulk`) also admits `tcgen05` instructions other
than `tcgen05.cp`, so it issues no Tensor Core copy (`Execution.TcBulk.no_cpIssue`). Its
`Execution.TcBulk.not_unsafe` leaves the kernel, besides the branches above, the Tensor Memory
branches (read sources, allocator resources, releases and accesses, commits, MMA writes, reads
and instructions); `Execution.MbarBulk.not_unsafe` is its instance without `tcgen05` events. Its
open obligations are its pending threads, linear copies, Tensor Core operations, commits and
allocator operations (`Execution.TcBulk.open_cases`), and a thread of the class is released when
its last event is no unreleased CTA barrier, warp-collective `tcgen05` event or paired allocator
operation (`Execution.TcBulk.released`). -/

namespace PTX

noncomputable section

/-- Whether an event kind is of the mbarrier/bulk class: not a tensor copy or prefetch, a
cluster launch control event, a cluster barrier operation, a `tcgen05` instruction, a register
request or a warp collective. -/
def Kind.isMbarBulk : Kind → Bool
  | .setMaxReg .. | .warpBar .. | .elect .. | .cluster .. | .clcQuery .. | .clcIssue ..
  | .tensorIssue .. | .tensorStore .. | .shfl .. | .tc .. | .tensorPrefetch .. | .matrix ..
  | .asyncArrive .. => false
  | _ => true

/-- Every event of `X` is of the mbarrier/bulk class. -/
def Execution.MbarBulk (X : Execution) : Prop :=
  ∀ v pc k, X.get v = some ⟨pc, k⟩ → k.isMbarBulk = true

/-- Whether an event kind is of the Tensor Core/mbarrier/bulk class: not a tensor copy or
prefetch, a cluster launch control event, a cluster barrier operation, a register request, a
warp collective or a Tensor Core copy (`tcgen05.cp`). -/
def Kind.isTcBulk : Kind → Bool
  | .setMaxReg .. | .warpBar .. | .elect .. | .cluster .. | .clcQuery .. | .clcIssue ..
  | .tensorIssue .. | .tensorStore .. | .shfl .. | .tensorPrefetch .. | .matrix ..
  | .asyncArrive .. | .tc (.cp ..) => false
  | _ => true

/-- Every event of `X` is of the Tensor Core/mbarrier/bulk class. -/
def Execution.TcBulk (X : Execution) : Prop :=
  ∀ v pc k, X.get v = some ⟨pc, k⟩ → k.isTcBulk = true

namespace Execution.TcBulk

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Without cluster-barrier events no cluster barrier faults. -/
theorem no_clusterFault (hn : X.TcBulk) : ¬ ClusterFault L X := by
  have hc : ∀ v pc op, X.get v ≠ some ⟨pc, .cluster op⟩ := fun v pc op he => by
    have := hn v pc _ he
    simp [Kind.isTcBulk] at this
  rintro ⟨c, -, s, -, r, err, hsrc, -, hp, hf⟩
  cases r with
  | exit g e =>
    simp only [ClusterBarrier.Record.perform, ClusterBarrier.perform] at hp
    split at hp
    · cases hp; simp [ClusterBarrier.Error.isFault] at hf
    · cases hp
  | arrival cta warp release lanes =>
    simp only [ClusterBarrier.Record.perform] at hp
    split at hp
    · rename_i hv
      obtain ⟨p, hp'⟩ := List.exists_mem_of_ne_nil lanes (fun hnil => by
        have := (of_decide_eq_true hv).2.2.2.1
        simp only [ne_eq, List.map_eq_nil_iff] at this
        exact this hnil)
      obtain ⟨-, -, pc, al, hg⟩ := hsrc p hp'
      exact hc _ _ _ hg
    · cases hp; simp [ClusterBarrier.Error.isFault] at hf
  | wait cta warp lanes =>
    simp only [ClusterBarrier.Record.perform] at hp
    split at hp
    · rename_i hv
      obtain ⟨p, hp'⟩ := List.exists_mem_of_ne_nil lanes (fun hnil => by
        have := (of_decide_eq_true hv).2.2.2.1
        simp only [ne_eq, List.map_eq_nil_iff] at this
        exact this hnil)
      obtain ⟨-, -, pc, al, hg⟩ := hsrc p hp'
      exact hc _ _ _ hg
    · cases hp; simp [ClusterBarrier.Error.isFault] at hf

/-- **No unsafe execution of the Tensor Core/mbarrier/bulk class**, given the branches the
kernel's own events decide: those of `Execution.MbarBulk.not_unsafe`, the Tensor Memory read
sources (`TcMma.SourceUnsafe`), the allocator's resources, releases and accesses, the commits, the
Tensor Memory writes and reads and the MMA instructions, and the shared-memory lifetimes. -/
theorem not_unsafe (hn : X.TcBulk) (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X)
    (hun : ¬ Unalloc mem0 X) (hord : ConflictsOrdered L X fun _ => True)
    (hbar : ¬ BarMismatch L X) (hfault : ¬ CtaBarFault L X) (htma : ¬ TmaUnsafe L mem0 X)
    (hsrc : ¬ TcMma.SourceUnsafe L A X) (hasm : ¬ ∃ a ∈ A, a.ub L mem0 X)
    (halign : ¬ AlignedMismatch L K X) (hwd : ¬ WarpDivergent L K A X)
    (hlife : ¬ SharedLifetimeUnsafe L K A X) (hpoll : ¬ PollShapeUnsafe K X)
    (huninit : ¬ MbarUninit L X) (hcred : ¬ TensorStore.CopyReduceNoRule A X)
    (hres : ¬ Tmem.Pair.ResourceUnsafe L X) (hrel : ¬ Tmem.Pair.ReleaseUnsafe L X)
    (hacc : ¬ Tmem.Pair.AccessUnsafe L X) (hcommit : ¬ TcCommitUnsafe L X)
    (hw : ¬ TcMma.WritesUnsafe L X) (hi : ¬ TcMma.InstructionUnsafe L A X)
    (hr : ¬ TcMma.ReadsUnsafe L X) :
    ¬ Unsafe L K A mem0 X := by
  have bad : ∀ {v pc k}, X.get v = some ⟨pc, k⟩ → k.isTcBulk = false → False :=
    fun he hk => by rw [hn _ _ _ he] at hk; cases hk
  have nt : ∀ i address s, ¬ X.TensorIssue i address s := by
    rintro i address s ⟨pc, hi⟩; exact bad hi rfl
  have ns : ∀ i address s, ¬ X.TensorStoreIssue i address s := by
    rintro i address s ⟨pc, hi⟩; exact bad hi rfl
  have np : ∀ i address s, ¬ X.TensorPrefetchIssue i address s := by
    rintro i address s ⟨pc, hi⟩; exact bad hi rfl
  have nc : ∀ i s ts, ¬ X.ClcIssue i s ts := by
    rintro i s ts ⟨pc, hi⟩; exact bad hi rfl
  have hempty : ∀ i, X.tensor i = none := fun i => by
    cases he : X.tensor i with
    | none => rfl
    | some o =>
      obtain ⟨addr, hi⟩ := (hX.tensor i o he).1
      exact (nt _ _ _ hi).elim
  intro hu
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  · exact hub h
  · exact hun h
  · exact hord.no_race h
  · exact hord.no_mixed h
  · exact hbar h
  · exact htma h
  · exact hsrc h
  · exact hasm h
  · exact halign h
  · exact hlife h
  · simp [ClcUnsafe, nc] at h
  · simp [TensorUnsafe, hempty] at h
  · have nred : ¬ TensorStore.ReduceNoRule A X := by
      rintro ⟨i, o, -, -, -, hio, -⟩
      obtain ⟨⟨addr, hi⟩, -⟩ := hX.store i o hio
      exact ns i addr o.spec hi
    exact h.elim nred hcred
  · simp [TensorAllocationUnsafe, nt, ns, np] at h
  · exact hres h
  · exact hrel h
  · exact hpoll h
  · exact hacc h
  · exact hcommit h
  · exact hw h
  · exact hi h
  · exact hr h
  · obtain ⟨e, pc, inc, n, inst, hi, -⟩ := h
    exact bad hi rfl
  · exact hfault h
  · exact hn.no_clusterFault h
  · exact hwd h
  · refine not_matrixUnsafe_of_none (L := L) (fun e ev he => ?_) h
    obtain ⟨pc, k⟩ := ev
    cases k <;> first | rfl | exact (bad he rfl).elim
  · exact huninit h

/-- No event of the class is a Tensor Core copy. -/
theorem no_cpIssue (hn : X.TcBulk) : ∀ e c, ¬ X.CpIssue e c :=
  fun e _ ⟨pc, he⟩ => by have := hn e pc _ he; simp [Kind.isTcBulk] at this

/-- **The open obligations** of an execution of the class are pending threads, unfinished bulk
copies and MMAs, undelivered commits and uncovered Tensor Memory allocator operations. -/
theorem open_cases (hn : X.TcBulk) {o : Descent.Obligation} (ho : Descent.Obl L X o) :
    (∃ g, o = .thread g) ∨ o = .bulk ∨ o = .mma ∨ o = .commit ∨ o = .tmem := by
  have bad : ∀ {v pc k}, X.get v = some ⟨pc, k⟩ → k.isTcBulk = false → False :=
    fun he hk => by rw [hn _ _ _ he] at hk; cases hk
  cases o with
  | thread g => exact .inl ⟨g, rfl⟩
  | bulk => exact .inr (.inl rfl)
  | mma => exact .inr (.inr (.inl rfl))
  | commit => exact .inr (.inr (.inr (.inl rfl)))
  | tmem => exact .inr (.inr (.inr (.inr rfl)))
  | arriveOn => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | clc => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | tensor => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | store => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim

/-- **A thread of the class is released** when its last event, if a CTA barrier operation, a
group wait or a blocking `tcgen05` event, is ready: no cluster barrier or register request
occurs. -/
theorem released (hn : X.TcBulk) {g : Nat}
    (hbar : ∀ pc id count mode, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .bar id count mode⟩ → Ready L X (g, (X.tr g).length - 1))
    (hgw : ∀ pc k, X.get (g, (X.tr g).length - 1) = some ⟨pc, k⟩ →
      (∃ mode n, k = .bulkWait mode n) ∨ (∃ n, k = .asyncWait n) →
      Ready L X (g, (X.tr g).length - 1))
    (htc : ∀ pc t, X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc t⟩ →
      t.resume = .blocking false → Ready L X (g, (X.tr g).length - 1)) :
    Step.Released L X g := by
  refine ⟨fun pc k hq hk => ?_⟩
  have hc := hn _ _ _ hq
  cases k
  case bar id count mode => exact hbar pc id count mode hq
  case bulkWait mode n => exact hgw pc _ hq (.inl ⟨mode, n, rfl⟩)
  case asyncWait n => exact hgw pc _ hq (.inr ⟨n, rfl⟩)
  case tc t => exact htc pc t hq hk
  all_goals simp [Kind.isTcBulk, Kind.resume] at hc hk

end Execution.TcBulk

namespace Execution.MbarBulk

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- No event of the class is a `tcgen05` instruction. -/
theorem noTc (hn : X.MbarBulk) : X.NoTc := fun e pc k he => by
  have := hn e pc _ he
  simp [Kind.isMbarBulk] at this

/-- An execution of the mbarrier/bulk class is of the Tensor Core/mbarrier/bulk class. -/
theorem tcBulk (hn : X.MbarBulk) : X.TcBulk := fun v pc k he => by
  have := hn v pc k he
  cases k <;> simp_all [Kind.isMbarBulk, Kind.isTcBulk]

/-- **No unsafe execution of the mbarrier/bulk class**, given the branches the kernel's own
events decide. -/
theorem not_unsafe (hn : X.MbarBulk) (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X)
    (hun : ¬ Unalloc mem0 X) (hord : ConflictsOrdered L X fun _ => True)
    (hbar : ¬ BarMismatch L X) (hfault : ¬ CtaBarFault L X) (htma : ¬ TmaUnsafe L mem0 X)
    (hasm : ¬ ∃ a ∈ A, a.ub L mem0 X) (halign : ¬ AlignedMismatch L K X)
    (hwd : ¬ WarpDivergent L K A X) (hlife : ¬ SharedLifetimeUnsafe L K A X)
    (hpoll : ¬ PollShapeUnsafe K X) (huninit : ¬ MbarUninit L X)
    (hcred : ¬ TensorStore.CopyReduceNoRule A X) :
    ¬ Unsafe L K A mem0 X :=
  hn.tcBulk.not_unsafe hX hub hun hord hbar hfault htma (fun h => h hn.noTc.sourceSafe) hasm
    halign hwd hlife hpoll huninit hcred
    (hn.noTc.not_resourceUnsafe hX.tmemPair)
    (hn.noTc.not_releaseUnsafe hX.tmemPair) hn.noTc.not_accessUnsafe
    (fun ⟨_, _, hc, _⟩ => hn.noTc.not_commit hc)
    hn.noTc.not_writesUnsafe hn.noTc.not_instructionUnsafe hn.noTc.not_readsUnsafe

/-- **The open obligations** of an execution of the class are pending threads and unfinished
bulk copies. -/
theorem open_cases (hn : X.MbarBulk) {o : Descent.Obligation} (ho : Descent.Obl L X o) :
    (∃ g, o = .thread g) ∨ o = .bulk := by
  have bad : ∀ {v pc k}, X.get v = some ⟨pc, k⟩ → k.isMbarBulk = false → False :=
    fun he hk => by rw [hn _ _ _ he] at hk; cases hk
  cases o with
  | thread g => exact .inl ⟨g, rfl⟩
  | bulk => exact .inr rfl
  | arriveOn => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | mma =>
    refine (ho fun _ hi => ?_).elim
    rcases hi with ⟨_, _, _, _, _, hi⟩ | ⟨_, _, hi⟩ | ⟨_, _, hi⟩ <;> exact (bad hi rfl).elim
  | clc => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | tensor => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | store => exact (ho fun _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | commit => exact (ho fun _ _ _ _ ⟨_, hi⟩ => (bad hi rfl).elim).elim
  | tmem => exact (ho fun _ _ _ _ _ hi => (bad hi rfl).elim).elim

/-- **A thread of the class is released** when its last event, if a CTA barrier operation or a
group wait, is ready: no cluster barrier, register request or `tcgen05` instruction occurs. -/
theorem released (hn : X.MbarBulk) {g : Nat}
    (hbar : ∀ pc id count mode, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .bar id count mode⟩ → Ready L X (g, (X.tr g).length - 1))
    (hgw : ∀ pc k, X.get (g, (X.tr g).length - 1) = some ⟨pc, k⟩ →
      (∃ mode n, k = .bulkWait mode n) ∨ (∃ n, k = .asyncWait n) →
      Ready L X (g, (X.tr g).length - 1)) :
    Step.Released L X g :=
  hn.tcBulk.released hbar hgw fun _ _ hq => (hn.noTc _ _ _ hq).elim

end Execution.MbarBulk

end

end PTX

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.NoAsync
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Lemmas.Flow.WarpUniform
public import Lemmas.MBarrier.BarrierOrdinal
public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # `SafeGoal` for an execution without asynchronous events

For an execution none of whose events is an mbarrier, bulk-copy, tensor, CLC, cluster-barrier,
register-pool or `tcgen05` event (`Execution.NoTma`, which every consistent execution of a kernel
without such instructions is: `noTma_of_consistent`), every branch of `Unsafe` that needs such an
event is empty. `Execution.NoTma.not_unsafe` dispatches them and leaves the kernel the branches its
own events decide:

* no undefined behaviour (`HasUb`) and no unallocated byte (`Unalloc`);
* conflicting accesses ordered at every byte (`ConflictsOrdered … fun _ => True`), which excludes
  races and mixed-size conflicts;
* CTA barriers matched (`BarMismatch`) and not faulting (`CtaBarFault`); without any barrier
  event both are empty (`no_barMismatch_of`, `no_ctaBarFault_of`);
* no assumption's undefined behaviour, and no warp-divergent guard (`not_warpDivergent` when the
  kernel has no uniform guard);
* every shared access in the accessing thread's own CTA (the shared-lifetime branch). -/

namespace PTX

noncomputable section

namespace Execution.NoTma

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Without asynchronous events no stage completes an issued operation: every completing stage
names an issuing event of an asynchronous instruction. -/
theorem not_finalStage (hn : X.NoTma) {i : EvId} {p : AsyncCopy.Part} :
    ¬ AsyncCopy.FinalStage X i p := by
  rintro (⟨s, m, ⟨pc, hi⟩, -⟩ | ⟨s, ⟨pc, hi⟩, -⟩ | ⟨m, noinc, ⟨pc, hi⟩, -⟩ |
    ⟨⟨d, s, accum, mask, ⟨pc, hi⟩⟩ | ⟨c, ⟨pc, hi⟩⟩ | ⟨s, ⟨pc, hi⟩⟩, -⟩ |
    ⟨s, targets, c, ⟨pc, hi⟩, -⟩ | ⟨a, s, ⟨pc, hi⟩, -⟩ | ⟨a, s, ⟨pc, hi⟩, -⟩ |
    ⟨s, rank, m, ⟨pc, hi⟩, -⟩) <;> cases hn _ _ _ hi

/-- Without asynchronous events, every shared use is an access of the accessing thread's own
CTA, which completes before that thread's exit. -/
theorem no_sharedLifetimeUnsafe (hn : X.NoTma) (hout : ∀ g, L.threads ≤ g → X.tr g = [])
    (hlocal : ∀ e a w, X.Access e a w → a.loc.space = .shared → a.loc.cta = e.1 / L.block) :
    ¬ SharedLifetimeUnsafe L K A X := by
  rintro ⟨e, owner, hu, hbad⟩
  rcases hu with ⟨-, ⟨a, w, ha, hs, hcta⟩ | ⟨addr, action, ha⟩⟩ | ⟨i, s, -, ⟨pc, hi⟩, -⟩ |
    ⟨i, address, s, x, y, k, -, ⟨pc, hi⟩, -⟩ | ⟨i, address, s, -, ⟨pc, hi⟩, -⟩ |
    ⟨i, p, -, hf, -⟩
  · obtain ⟨i, rfl, ha⟩ := intent_thread hn ha
    have hown : owner = i.1 / L.block := hcta.symm.trans (hlocal _ _ _ ha hs)
    rcases hbad with ⟨hne, -⟩ | ⟨hx, hfin⟩
    · exact hne hown
    · exact hfin (SharedFinished.of_access hout ha hown.symm hx)
  · rw [hn.objectAction_none] at ha; cases ha
  · cases hn _ _ _ hi
  · cases hn _ _ _ hi
  · cases hn _ _ _ hi
  · exact not_finalStage hn hf

/-- Without cluster-barrier events no cluster barrier faults: a faulting record names an issued
cluster instruction. -/
theorem no_clusterFault (hn : X.NoTma) : ¬ ClusterFault L X := by
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
      cases hn _ _ _ hg
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
      cases hn _ _ _ hg
    · cases hp; simp [ClusterBarrier.Error.isFault] at hf

/-- Without barrier events, barriers are matched. -/
theorem no_barMismatch_of (hn : X.NoTma) (hnb : ∀ e id count pc, ¬ X.IsBarrier e id count pc) :
    ¬ BarMismatch L X := by
  rintro (⟨g, h, i, j, id, id', count, count', pc, pc', -, hb, -⟩ |
    ⟨g, h, i, j, id, id', count, count', mode', pc, pc', -, hb, -⟩)
  · exact hnb _ _ _ _ hb
  · cases hn _ _ _ hb

/-- Without barrier events, no CTA barrier faults. -/
theorem no_ctaBarFault_of [Fact K.NoBarArrive] (hX : Consistent L K A mem0 X)
    (hnb : ∀ e id count pc, ¬ X.IsBarrier e id count pc) : ¬ CtaBarFault L X :=
  not_ctaBarFault hX fun _ _ _ _ _ _ _ _ h _ => (hnb _ _ _ _ h).elim

/-- **No unsafe execution without asynchronous events**, given the branches the kernel's own
events decide. -/
theorem not_unsafe (hn : X.NoTma) (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X)
    (hun : ¬ Unalloc mem0 X) (hord : ConflictsOrdered L X fun _ => True)
    (hbar : ¬ BarMismatch L X) (hfault : ¬ CtaBarFault L X)
    (hasm : ¬ ∃ a ∈ A, a.ub L mem0 X) (halign : ¬ AlignedMismatch L K X)
    (hwd : ¬ WarpDivergent L K A X)
    (hlocal : ∀ e a w, X.Access e a w → a.loc.space = .shared → a.loc.cta = e.1 / L.block) :
    ¬ Unsafe L K A mem0 X := by
  have nt : ∀ i address s, ¬ X.TensorIssue i address s := by
    rintro i address s ⟨pc, hi⟩; cases hn _ _ _ hi
  have ns : ∀ i address s, ¬ X.TensorStoreIssue i address s := by
    rintro i address s ⟨pc, hi⟩; cases hn _ _ _ hi
  have np : ∀ i address s, ¬ X.TensorPrefetchIssue i address s := by
    rintro i address s ⟨pc, hi⟩; cases hn _ _ _ hi
  have nc : ∀ i s ts, ¬ X.ClcIssue i s ts := by
    rintro i s ts ⟨pc, hi⟩; cases hn _ _ _ hi
  have hempty : ∀ i, X.tensor i = none := fun i => (hn.other_empty hX i).1
  intro hu
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  · exact hub h
  · exact hun h
  · exact hord.no_race h
  · exact hord.no_mixed h
  · exact hbar h
  · exact hn.not_tmaUnsafe (hn.objects_empty hX) h
  · exact h hn.sourceSafe
  · exact hasm h
  · exact halign h
  · exact no_sharedLifetimeUnsafe hn hX.outside hlocal h
  · simp [ClcUnsafe, nc] at h
  · simp [TensorUnsafe, hempty] at h
  · rcases h with ⟨i, o, -, -, -, hio, -⟩ | ⟨i, s, -, -, ⟨pc, hi⟩, -⟩
    · obtain ⟨⟨addr, hi⟩, -⟩ := hX.store i o hio
      exact ns i addr o.spec hi
    · cases hn _ _ _ hi
  · simp [TensorAllocationUnsafe, nt, ns, np] at h
  · exact hn.noTc.not_resourceUnsafe hX.tmemPair h
  · exact hn.noTc.not_releaseUnsafe hX.tmemPair h
  · obtain ⟨e, pc, m, q, ok, acq, sc, he, -⟩ := h
    cases hn _ _ _ he
  · exact hn.noTc.not_accessUnsafe h
  · obtain ⟨_, _, hc, _⟩ := h
    exact hn.noTc.not_commit hc
  · exact hn.noTc.not_writesUnsafe h
  · exact hn.noTc.not_instructionUnsafe h
  · exact hn.noTc.not_readsUnsafe h
  · obtain ⟨e, pc, inc, n, inst, hi, -⟩ := h
    cases hn _ _ _ hi
  · exact hfault h
  · exact no_clusterFault hn h
  · exact hwd h
  · refine not_matrixUnsafe_of_none (L := L) (fun e ev he => ?_) h
    obtain ⟨pc, k⟩ := ev
    have hk := hn _ _ _ he
    cases k <;> first | rfl | (simp [Kind.isTma] at hk)
  · obtain ⟨e, m, hu, -⟩ := h
    exact hn.not_usesMbar hu

end Execution.NoTma

end

end PTX

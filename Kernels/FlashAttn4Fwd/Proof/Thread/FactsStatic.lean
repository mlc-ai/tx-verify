-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.ElectFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Kernels.FlashAttn4Fwd.Proof.Interface.Result
public import Lemmas.Flow.ElectLead
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotBulkPrefetch
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotTcShift
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.TensorStoreBase
public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.NotTensorPrefetch
public import Lemmas.Flow.WaitLoopPcs
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll
public import Lemmas.Clc.ClcExecution
public import Lemmas.Flow.WaitAcquire
public import Lemmas.Execution.NoTcCp

@[expose] public section

/-! # The thread facts decided on the code

Facts of every consistent execution that need no machine, only that each event is fired by the
instruction at its position (`Flow.get_source`):

* **Elections.** Every election has the full mask (`elect_full`), so each thread either led
  every election of its trace or none (`Static.elect_dichotomy`, by `ElectOk.deterministic`); a
  thread that did not lead none before an event led one there (`Static.leadAt_of_not_nonLead`).
* **Absent instructions.** The code has no bulk copy, cancellation request, invalidation, tensor
  prefetch or `tcgen05.cp`, so no event is one; no thread is cancelled.
* **Tensor stores.** A tensor store's source is a `.shared::cta` address, in its issuer's CTA
  (`AsyncFacts_store_base`).
* **Polls and arrivals.** Every `mbarrier.try_wait` heads a wait loop, so every successful poll
  is the poll of a canonical spin (`kernel_spins`, `RingFacts_spins`); every poll acquires and
  every arrival releases, at cluster scope at the sites of `Assumptions.clusterMbar`
  (`Static.wait_attr`, `Static.arrive_attr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Elections -/

/-- Every election of a thread's trace has the full mask. -/
theorem Static.elect_mask (hX : Consistent L kernel asms mem0 X) (g : Nat) :
    ElectMask 4294967295 (X.tr g) := fun _ he _ _ _ hk => by
  obtain ⟨j, hj⟩ := elect_of_mem he hk
  exact elect_full hX hj

/-- **A thread led every election of its trace, or none.** -/
theorem Static.elect_dichotomy (hX : Consistent L kernel asms mem0 X) (g : Nat) :
    ElectLead L g (X.tr g) ∨ ElectNonLead L g (X.tr g) :=
  electLead_or_nonLead hX.elect (Static.elect_mask hX g)

/-- The dichotomy on each prefix of the trace. -/
theorem Static.elect_dichotomy_take (hX : Consistent L kernel asms mem0 X) (g k : Nat) :
    ElectLead L g ((X.tr g).take k) ∨ ElectNonLead L g ((X.tr g).take k) :=
  (Static.elect_dichotomy hX g).imp (·.take k) (·.take k)

/-- A thread that led some election before event `k` led a full-mask one there. -/
theorem Static.leadAt_of_not_nonLead (hX : Consistent L kernel asms mem0 X) {g k : Nat}
    (h : ¬ ElectNonLead L g ((X.tr g).take k)) : LeadAt L X g k := by
  simp only [ElectNonLead, not_forall, not_not] at h
  obtain ⟨e, he, mask, inst, ld, hk, hld⟩ := h
  obtain ⟨j, hj, he'⟩ := List.getElem_of_mem he
  have hj' : j < k := by simp at hj; omega
  have hget : X.get (g, j) = some e := by
    show (X.tr g)[j]? = some e
    rw [← he', List.getElem_take]
    exact List.getElem?_eq_getElem _
  have hE : X.Elect (g, j) e.pc mask inst ld := by
    show X.get (g, j) = some ⟨e.pc, .elect mask inst ld⟩
    rw [hget, ← hk]
  have hm := elect_full hX hE
  subst hm hld
  exact ⟨j, hj', e.pc, inst, hE⟩

/-! ### Absent instructions -/

theorem kernel_noBulk : kernel.code.all (fun ins => !bulkOp ins.op) = true := by decide +kernel

theorem kernel_noInval : kernel.code.all (fun ins => !invalOp ins.op) = true := by
  decide +kernel

theorem kernel_noClc : kernel.code.all (fun ins => !clcOp ins.op) = true := by decide +kernel

theorem kernel_noPrefetch : kernel.code.all (fun ins => !tensorPrefetchOp ins.op) = true := by
  decide +kernel

theorem kernel_noTcCp : kernel.NoTcCp = true := by decide +kernel

theorem kernel_noAsyncArrive : kernel.code.all (fun ins => !asyncArriveOp ins.op) = true := by
  decide +kernel

theorem kernel_noBulkPrefetch : kernel.code.all (fun ins => !bulkPrefetchOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no asynchronous copy.** -/
theorem TmemFacts_no_bulk (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩ :=
  fun he => no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk)
    kernel_noBulk he ⟨_, rfl⟩

/-- **The kernel has no `cp.async.mbarrier.arrive`.** -/
theorem TmemFacts_no_arriveOn (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {m : Loc} {noinc : Bool}, X.get i ≠ some ⟨pc, .asyncArrive m noinc⟩ :=
  fun he => no_kind_of_code hX asyncArriveOp (fun k => ∃ m n, k = .asyncArrive m n)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_asyncArrive_op hf hk)
    kernel_noAsyncArrive he ⟨_, _, rfl⟩

theorem kernel_noAtomic : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no atomic read-modify-write.** -/
theorem TmemFacts_no_rmw (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {a : Acc} {old : List (Option Byte)} {new : Option (List Byte)},
      X.get i ≠ some ⟨pc, .rmw a old new⟩ :=
  fun he => no_kind_of_code hX atomicOp (fun k => ∃ a o n, k = .rmw a o n)
    (fun _ ⟨_, _, _, h⟩ => by cases h) (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk)
    kernel_noAtomic he ⟨_, _, _, rfl⟩

/-- **The kernel has no bulk prefetch.** -/
theorem TmemFacts_no_prefetch (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {a : Acc}, X.get i ≠ some ⟨pc, .bulkPrefetch a⟩ :=
  fun he => no_kind_of_code hX bulkPrefetchOp (fun k => ∃ a, k = .bulkPrefetch a)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulkPrefetch_op hf hk)
    kernel_noBulkPrefetch he ⟨_, rfl⟩

/-- **The kernel has no cancellation request.** -/
theorem TmemFacts_no_clc (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat},
      X.get i ≠ some ⟨pc, .clcIssue sp tg⟩ :=
  fun he => no_kind_of_code hX clcOp (fun k => ∃ s t, k = .clcIssue s t)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk)
    kernel_noClc he ⟨_, _, rfl⟩

/-- **The kernel has no barrier invalidation.** -/
theorem TmemFacts_no_inval (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {m : Loc}, X.get i ≠ some ⟨pc, .mbInval m⟩ :=
  fun he => no_kind_of_code hX invalOp (fun k => ∃ m, k = .mbInval m)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_mbInval_op hf hk)
    kernel_noInval he ⟨_, rfl⟩

/-- **The kernel issues no tensor prefetch.** -/
theorem AsyncFacts_no_prefetch (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc a : Nat} {s : TensorPrefetch.Spec},
      X.get i ≠ some ⟨pc, .tensorPrefetch a s⟩ :=
  fun he => no_kind_of_code hX tensorPrefetchOp (fun k => ∃ a s, k = .tensorPrefetch a s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_tensorPrefetch_op hf hk)
    kernel_noPrefetch he ⟨_, _, rfl⟩

/-- **The kernel has no `tcgen05.cp`.** -/
theorem ScoreFacts_no_cp (hX : Consistent L kernel asms mem0 X) :
    ∀ e c, ¬ X.CpIssue e c :=
  noCp_of_consistent kernel_noTcCp hX

theorem kernel_noTcShift : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no `tcgen05.shift`.** -/
theorem ScoreFacts_no_shift (hX : Consistent L kernel asms mem0 X) :
    ∀ e s, ¬ X.ShiftIssue e s :=
  fun _ _ ⟨_, he⟩ => no_kind_of_code hX tcShiftOp (fun k => ∃ s, k = .tc (.shift s))
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_tcShift_op hf hk)
    kernel_noTcShift he ⟨_, rfl⟩

/-- **No thread is cancelled**: a cancellation needs a request, and the kernel issues none. -/
theorem WriteFacts_started (hX : Consistent L kernel asms mem0 X) :
    ∀ g < L.threads, ¬ ClcCanceled L X g := by
  rintro g - ⟨-, req, ho⟩
  obtain ⟨i, s, targets, -, ⟨pc, hi⟩, -⟩ := ClcOk.canceled_has_issue hX.clc ho
  exact TmemFacts_no_clc hX hi

/-- **A tensor store reads its own CTA**: its source is a `.shared::cta` address. -/
theorem AsyncFacts_store_base (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue i a s →
      s.sharedBase.cta = ctaOf L i.1 := by
  rintro i a s ⟨pc, he⟩
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, -, hf⟩
  · cases hf
  · exact fires_tensorStore_base hf rfl

/-- No store instruction of the kernel names global memory (decided on the code). -/
theorem kernel_noGlobalStore :
    kernel.code.all (fun ins => storeSpace ins.op != some .global && !dynamicAccess ins.op) =
      true := by
  decide +kernel

/-- **Every global write is a tensor store's**: the threads' stores name shared memory, a tensor
load writes shared memory (its route, `TensorOk`), and the kernel has no cancellation request
and no bulk copy. -/
theorem WriteFacts_global (hX : Consistent L kernel asms mem0 X) :
    ∀ w a bs, X.MemWrites w a bs → a.loc.space = .global →
      ∃ i x y k, w = .async i (.write (.store x y k)) := by
  intro w a bs hw hgl
  rcases w with e | ⟨i, p⟩
  · exfalso
    rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    swap
    · exact TmemFacts_no_rmw hX he
    rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
    · cases hf
    have hall := List.all_eq_true.mp kernel_noGlobalStore ins (List.mem_of_getElem? hc)
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hall
    rcases fires_write_space hf rfl with hsp | hd
    · rw [hsp, hgl] at hall
      simp at hall
    · simp [hd] at hall
  · cases p with
    | writeStore x y k => exact ⟨i, x, y, k, rfl⟩
    | writeLoad x y z =>
      exfalso
      obtain ⟨o, addr, b, ho, -, hloc, -⟩ := hw
      have hs : o.spec.sharedBase.space = .shared := (hX.tensor i o ho).2.2.1.2.1
      simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hloc
      obtain ⟨slot, -, hl⟩ := hloc
      rw [← hl] at hgl
      simp only [TensorBox.sharedLoc] at hgl
      rw [hs] at hgl
      cases hgl
    | writeCta c =>
      obtain ⟨s, targets, ⟨pc, hi⟩, -⟩ := hw
      exact absurd hi (TmemFacts_no_clc hX)
    | writeCopy =>
      obtain ⟨s, ⟨pc, hb⟩, -⟩ := hw
      exact absurd hb (TmemFacts_no_bulk hX)
    | writeElem j =>
      obtain ⟨s, ⟨pc, hb⟩, -⟩ := hw
      exact absurd hb (TmemFacts_no_bulk hX)
    | _ => exact hw.elim

/-! ### Polls and arrivals -/

/-- Every poll of the kernel is at a listed position (decided on the code). -/
theorem kernel_poll_pcs : OpPcsFast kernel.code pollOp Flow.mbarWait.toList = true := by
  decide +kernel

/-- Every listed poll heads a wait loop that no branch enters, and its predicate is read nowhere
but in the loop's branch (decided on the code). -/
theorem kernel_wait_loops : kernel.waitLoopPcs Flow.mbarWait.toList = true := by
  decide +kernel

/-- **Every successful wait of a thread is the poll of a canonical spin**: it fires from a poll
of the code, which is listed and heads a wait loop (`Kernel.canonicalSpin_of_waitLoopPcs`). -/
theorem kernel_spins (hX : Consistent L kernel asms mem0 X) {i : EvId} {pc p : Nat} {m : Loc}
    {acq : Bool} {sc : MbarScope} (he : X.get i = some ⟨pc, .wait m p true acq sc⟩) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
    · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
      exact Kernel.canonicalSpin_of_waitLoopPcs kernel_poll_pcs kernel_wait_loops hc hop
    · push Not at hw
      exact absurd rfl (fires_notWait (eventTmpl_notWait hw) hf m p true acq sc)

/-- **Every successful poll is the poll of a canonical spin.** -/
theorem RingFacts_spins (hX : Consistent L kernel asms mem0 X) :
    ∀ {g k pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}, g < L.threads →
      X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ → ∃ exit, kernel.CanonicalSpin pc exit :=
  fun _ he => kernel_spins hX he

/-- Every poll instruction acquires at CTA scope, every arrival releases at CTA scope (decided
on the code). -/
theorem kernel_wait_flags : kernel.code.all (fun ins => match ins.op with
    | .mbarWait _ _ _ _ acq sc => acq && sc == .cta
    | _ => true) = true := by
  decide +kernel

theorem kernel_arrive_flags : kernel.code.all (fun ins => match ins.op with
    | .mbarArrive _ _ _ _ _ rel sc _ => rel && sc == .cta
    | _ => true) = true := by
  decide +kernel

/-- The sites `Assumptions.clusterMbar` widens to cluster scope. -/
theorem asms_clusterScopeMbar (pc : Nat) :
    asms.any (·.clusterScopeMbar pc) = Assumptions.clusterMbarSites.contains pc := by
  simp [asms, Assumptions.all, Assumptions.idealArith, Assumptions.clusterMbar,
    Assumptions.approx, Assumptions.swExp2, Assumptions.peerBit, Assumptions.tcLd,
    Assumptions.commitOrder, Assumptions.pollAgree, Assumption.idealReal,
    Assumption.clusterScopeMbarAt, Assumption.approxExact, Assumption.segmentExact,
    Assumption.pairEvenAt, Assumption.tcLdDataflowAt, Assumption.commitOrderAt,
    Assumption.pollAgreeAt]

/-- **A poll acquires**, at cluster scope at a site of `Assumptions.clusterMbar`. -/
theorem Static.wait_attr (hX : Consistent L kernel asms mem0 X) {i : EvId} {pc p : Nat}
    {m : Loc} {ok acq : Bool} {sc : MbarScope} (he : X.get i = some ⟨pc, .wait m p ok acq sc⟩) :
    acq = true ∧ (pc ∈ Assumptions.clusterMbarSites → sc = .cluster) := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, htpc, hc, hf⟩
  · cases hf
  obtain ⟨p', b, off, par, sc0, hop, hw⟩ := fires_wait_flags hf rfl
  have hall := List.all_eq_true.mp kernel_wait_flags ins (List.mem_of_getElem? hc)
  rw [hop] at hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  refine ⟨hall.1, fun hs => hw ?_ hall.1 hall.2⟩
  rw [htpc, asms_clusterScopeMbar]
  exact List.contains_iff_mem.mpr hs

/-- **An arrival releases**, at cluster scope at a site of `Assumptions.clusterMbar`. -/
theorem Static.arrive_attr (hX : Consistent L kernel asms mem0 X) {i : EvId} {pc tx c : Nat}
    {m : Loc} {rel : Bool} {sc : MbarScope} (he : X.get i = some ⟨pc, .arrive m tx c rel sc⟩) :
    rel = true ∧ (pc ∈ Assumptions.clusterMbarSites → sc = .cluster) := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, htpc, hc, hf⟩
  · cases hf
  obtain ⟨b, off, tx', c', cl, sc0, st, hop, hw⟩ := fires_arrive_flags hf rfl
  have hall := List.all_eq_true.mp kernel_arrive_flags ins (List.mem_of_getElem? hc)
  rw [hop] at hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  refine ⟨hall.1, fun hs => hw ?_ hall.1 hall.2⟩
  rw [htpc, asms_clusterScopeMbar]
  exact List.contains_iff_mem.mpr hs

end
end PTX.Kernels.FlashAttn4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.SyncCluster
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds
public import Lemmas.Async.BulkGroup
public import Lemmas.TensorStore.TensorStore
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # `TensorStoreUnsafe` and the tensor stores' source lifetimes, from the thread facts

The kernel's tensor stores are not reductions (`no_reduce`) and it issues no linear copy
(`no_copy`). A TMA store's source storage is its issuer's CTA's staging buffer; when that
CTA has exited, the issuer has exited, and before its exit it made its final drain
(`ThreadFacts.cons_exit_drain`): a bulk wait for every group, right after a bulk commit that follows
every tensor store of the thread. That wait covers the store's group, so its return needs the
store's read completion, which is therefore present and a witness of the wait; the wait is
blocking, so its return enables the exit (`store_reads_finished`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX AsyncCopy

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The bulk actions of a trace followed by one more event. -/
theorem bulkActions_snoc (g : Nat) (xs : List Event) (e : Event) :
    bulkActions g (xs ++ [e]) = bulkActions g xs ++ (bulkAction g xs.length e.kind).toList := by
  unfold bulkActions
  rw [List.zipIdx_append, List.filterMap_append]
  simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.filterMap_cons,
    List.filterMap_nil]
  cases bulkAction g xs.length e.kind <;> simp

/-- **A final drain observes every earlier tensor store.** A bulk wait of every group, right after a
bulk commit, observes every tensor store before them. -/
theorem final_drain_waits {g j pcw pcc old oldPc address : Nat} {mode : BulkGroup.WaitMode}
    {spec : TensorStore.Spec}
    (hwait : X.get (g, j) = some ⟨pcw, .bulkWait mode 0⟩)
    (hcommit : X.get (g, j - 1) = some ⟨pcc, .bulkCommit⟩) (hj : 0 < j)
    (hold : X.get (g, old) = some ⟨oldPc, .tensorStore address spec⟩) (hlt : old < j - 1) :
    BulkWaitsFor X mode (g, old) (g, j) := by
  have hlen : j - 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hcommit).1
  have htake : (X.tr g).take j = (X.tr g).take (j - 1) ++ [⟨pcc, .bulkCommit⟩] := by
    have h1 : j = (j - 1) + 1 := by omega
    rw [h1, List.take_add_one]
    simp only [Nat.add_sub_cancel]
    have : (X.tr g)[j - 1]? = some ⟨pcc, .bulkCommit⟩ := hcommit
    rw [this]
    rfl
  have hplen : ((X.tr g).take (j - 1)).length = j - 1 := by
    simp only [List.length_take]
    omega
  have hactions : bulkActions g ((X.tr g).take j) =
      bulkActions g ((X.tr g).take (j - 1)) ++ [.commit] := by
    rw [htake, bulkActions_snoc, hplen]
    rfl
  have hold' : ((X.tr g).take (j - 1))[old]? = some ⟨oldPc, .tensorStore address spec⟩ := by
    rw [List.getElem?_take_of_lt hlt]
    exact hold
  have ha : BulkGroup.Action.issue (g, old) ∈ bulkActions g ((X.tr g).take (j - 1)) := by
    apply List.mem_filterMap.mpr
    exact ⟨(⟨oldPc, .tensorStore address spec⟩, old),
      List.mem_zipIdx_iff_getElem?.mpr hold', rfl⟩
  have hm : (g, old) ∈ (BulkGroup.run (bulkActions g ((X.tr g).take (j - 1)))).groups.flatten ++
      (BulkGroup.run (bulkActions g ((X.tr g).take (j - 1)))).pending := by
    rw [BulkGroup.run_members]
    exact List.mem_filterMap.mpr ⟨.issue (g, old), ha, rfl⟩
  refine ⟨pcw, 0, hwait, ?_⟩
  change BulkGroup.Observes (BulkGroup.run _) 0 _
  rw [hactions]
  unfold BulkGroup.run
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, BulkGroup.step, BulkGroup.observes_zero]
  rcases List.mem_append.mp hm with hg | hp
  · obtain ⟨group, hgroup, ho⟩ := List.mem_flatten.mp hg
    exact ⟨group, List.mem_append_left _ hgroup, ho⟩
  · exact ⟨_, by simp [BulkGroup.run], hp⟩

/-- **A tensor store's source reads finish before the exit of its issuer's CTA.** -/
theorem store_reads_finished (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {i : EvId} {address : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i address s)
    (hexit : CtaExited L X s.sharedBase.cta) :
    SharedFinished L kernel Prod X (.async i .readsDone) s.sharedBase.cta := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨hcta, -⟩ := ht.store_box hg he hσ rfl
  obtain ⟨c, rfl⟩ := (ht.access_region hg he hσ).2.2 address s rfl
  have hrw := ht.role_warp hg (len_of_get he).le hσ
  simp only [roleWarp] at hrw
  obtain ⟨pcx, hlast⟩ := hexit g hg hcta.symm
  have hlen : k < (X.tr g).length := len_of_get he
  have hexit_get : X.get (g, (X.tr g).length - 1) = some ⟨pcx, .exit⟩ := by
    simpa only [Execution.get, List.getLast?_eq_getElem?] using hlast
  have hkx : k < (X.tr g).length - 1 := by
    rcases Nat.lt_or_ge k ((X.tr g).length - 1) with h | h
    · exact h
    · have : k = (X.tr g).length - 1 := by omega
      subst this
      rw [he] at hexit_get
      cases hexit_get
  obtain ⟨dx, hdx⟩ := Frame.event_state ht.sound hX ht.tracked hexit_get nofun
  obtain ⟨j, pcw, pcc, hj, hjk, hjw, hjc, hnos⟩ :=
    ht.cons_exit_drain hg hexit_get hdx (by omega)
  have hkj : k < j - 1 := by
    by_contra hn
    have hkj' : k ≠ j - 1 := by
      intro h
      rw [h, hjc] at he
      cases he
    by_cases hjk' : j ≤ k
    · exact hnos k hjk' hkx pc address s he
    · omega
  have hbw := final_drain_waits hjw hjc hj he hkj
  have hret : Returned X (g, j) := by
    simp only [Returned, hjw, Kind.resume]
    omega
  have hneed : Need.node (· = Ref.async (g, k) .readsDone) ∈ Needs L X (g, j) := by
    simp only [Needs, hjw, KindNeeds, groupNeeds, needsIf]
    refine List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega), ?_⟩
    rw [ite_eq_left (show GroupWaitsFor X (.bulk .full) (g, k) (g, j) from hbw)]
    exact List.mem_map.mpr ⟨.readsDone, by simp [GroupWaitStages, he], rfl⟩
  obtain ⟨y, hpresent, rfl⟩ := hX.dependency.ready _ hret _ hneed
  have hwit : Witness L X (.async (g, k) .readsDone) (g, j) := Witness.of_need L hneed hpresent rfl
  exact SharedFinished.of_observer_exit (finish := (g, (X.tr g).length - 1)) hpresent hwit
    ⟨⟨rfl, hjk, by simp only; omega⟩, by simp [hjw, Kind.resume]⟩
    ⟨hg, hcta.symm, pcx, hexit_get⟩

/-- The kernel's tensor stores are not reductions. -/
theorem no_reduce (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X) :
    ∀ i addr s, X.TensorStoreIssue i addr s → s.reduce = none := by
  rintro ⟨g, k⟩ addr s ⟨pc, he⟩
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ : ∃ d, Frame.stateAt (code L) X g k = some (some d) := by
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
    exact ⟨d, hσ⟩
  obtain ⟨c, rfl⟩ := (ht.access_region hg he hσ).2.2 addr s rfl
  obtain ⟨-, -, -, -, -, -, hred, -⟩ := ht.store_tile hg he hσ
  exact hred

/-- **No reduction is unsafe.** The kernel's tensor stores are not reductions (`no_reduce`) and it
issues no linear copy (`no_copy`), so no reduction element lacks an arithmetic rule. -/
theorem no_tensorStoreUnsafe (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ TensorStoreUnsafe Prod X := by
  rintro (⟨i, o, red, x, y, hio, hred, -⟩ | h)
  · obtain ⟨⟨addr, hi⟩, -⟩ := hX.store i o hio
    rw [no_reduce ht hX i addr o.spec hi] at hred
    cases hred
  · exact TensorStore.not_copyReduceNoRule_of_none (fun i s hc => (no_copy hX ht hc).elim) h

end PTX.Kernels.Fp16Gemm8192.Proof.Safety

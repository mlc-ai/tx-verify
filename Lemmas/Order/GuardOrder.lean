-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.Order.DependencyWitness
public import Lemmas.Execution.EffectValidity
public import Lemmas.Async.AsyncChain
public import Lemmas.Async.AsyncMBarrier

@[expose] public section

/-! Synchronization through guarded instructions is a dependency.

When every successful mbarrier wait of an execution is the poll of a canonical spin
(`Kernel.CanonicalSpin`) and no synchronization goes through a release/acquire memory read
(`synchronizesWith`), each `baseCausality` path that starts at the return of a guard (a canonical
spin's successful poll or a blocking return) is a `DepStep` path: program order after a guard is a
return edge (`DepStep.of_resumes`), and each synchronizes-with edge of `baseCausality` is a witness
(arrival → acquire wait, barrier participant → return) followed by a guard (`DepStep.of_witness`).
This is how `DepStepAcyclic` orders an asynchronous operation's issue after the observation of its
completion is excluded. -/

namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Every successful mbarrier wait is the poll of a canonical spin, no `baseCausality` edge is a
release/acquire memory read or a release/acquire pattern around a fence, and no record up to a
successful wait of its object faults. A kernel discharges it from its code
(`Kernel.CanonicalSpin`, no release stores) and its objects' fault freedom. -/
structure SyncGuarded (L : Launch) (K : Kernel) (X : Execution) : Prop where
  spin : ∀ w pc m q acq sc,
    X.get w = some ⟨pc, .wait m q true acq sc⟩ → ∃ exit, K.CanonicalSpin pc exit
  noMemSync : ∀ e f, ¬ synchronizesWith L X e f ∧ ¬ FenceSync L X e f
  noFault : ∀ m (i j : Nat) (r w : MBarrier.Record AsyncCopy.Ref), (X.objects m)[i]? = some r →
    (X.objects m)[j]? = some w →
    w.reply.waited = some true → i ≤ j → r.fault = none

/-- The fields of `Consistent` that a guarded `baseCausality` step reads: the readiness of
DEP-ORDER, the CTA barrier histories (OBJ-CTA-BARRIER-SYNC), the cluster barrier histories
(OBJ-CLUSTER-BARRIER-SYNC) and the warp barrier instances (DEP-WARP-BARRIER). A bundle of existing
Core obligations; it introduces no execution rule. -/
structure GuardOk (L : Launch) (X : Execution) : Prop where
  ready : ∀ e, Returned X e → Ready L X e
  ctaBar : CtaBarHistoryOk L X
  cluster : ClusterHistoryOk L X
  warpBar : WarpBarOk L X

theorem Consistent.guardOk (hX : Consistent L K A mem0 X) : GuardOk L X :=
  ⟨hX.dependency.ready, hX.ctaBar, hX.cluster, hX.warpBar⟩

/-- The return of `w` guards each later instruction of its thread: `w` is the successful poll of a
canonical spin, or a blocking event that has returned (`Resumes`). -/
def GuardSource (K : Kernel) (X : Execution) (w : EvId) : Prop :=
  (∃ pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ ∧
    ∃ exit, K.CanonicalSpin pc exit) ∨
  (∃ ev b, X.get w = some ev ∧ ev.kind.resume = .blocking b)

theorem GuardSource.guard {w f : EvId} (hw : GuardSource K X w) (h : TraceBefore X w f) :
    DepStep L K X (.thread w, true) (.thread f, false) := by
  rcases hw with ⟨pc, m, q, acq, sc, hget, exit, hcanon⟩ | ⟨ev, b, hget, hres⟩
  · have hr : Resumes K X w f := by
      refine ⟨h, ?_⟩
      simp only [hget, Kind.resume]
      exact ⟨pc, exit, m, q, acq, sc, hget, hcanon, h⟩
    exact DepStep.of_resumes (L := L) hr
  · exact DepStep.of_resumes (L := L) (Resumes.of_blocking hget hres h)

/-- A successful poll of a canonical spin is a guard. -/
theorem SyncGuarded.wait (hg : SyncGuarded L K X) {w : EvId} {pc : Nat} {m : Loc} {q : Nat}
    {acq : Bool} {sc : MbarScope} (h : X.get w = some ⟨pc, .wait m q true acq sc⟩) :
    GuardSource K X w :=
  .inl ⟨pc, m, q, acq, sc, h, hg.spin w pc m q acq sc h⟩

/-- A release arrival recorded on its object is a counted update of that object. -/
theorem arrive_counter (ho : AsyncCopy.ObjectsOk X) {x : EvId} {m : Loc} {pc tx count : Nat}
    {rel : Bool} {sc : MbarScope} (hx : X.get x = some ⟨pc, .arrive m tx count rel sc⟩)
    {m' : Loc} {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects m')
    (hid : r.id = .thread x) :
    CounterUpdate r.action := by
  have h := ((ho m').2.1 r hr).1
  rw [hid] at h
  simp only [AsyncCopy.objectAction, hx] at h
  split_ifs at h
  rw [← Option.some.inj h]
  trivial

/-- One base step of `baseCausality` after a guard keeps a guard behind the target. Every
counter synchronisation case needs `GuardOk`: a CTA barrier return releases the generation its
`CtaBarK` names (`ctaBarDone_of_ready`, `hok.ready`) and that key is the arrival's own
(`CtaBarK.key_unique`, `hok.ctaBar`), a cluster wait has its `.wait` instruction from
`ClusterSources` (`hok.cluster`), and a warp barrier instance gives its witness through `WarpBarOk`
(`hok.warpBar`). -/
theorem guard_step (hg : SyncGuarded L K X) (ho : AsyncCopy.ObjectsOk X)
    (hok : GuardOk L X) {w a b : EvId}
    (hI : ∃ g, Relation.ReflTransGen (DepStep L K X) (.thread w, true) (.thread g, true) ∧
      GuardSource K X g ∧
        (TraceBefore X g a ∨ (g = a ∧ ∀ m tx count sc, ¬ X.Arrive a m tx count true sc)))
    (h : po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b) :
    ∃ g, Relation.ReflTransGen (DepStep L K X) (.thread w, true) (.thread g, true) ∧
      GuardSource K X g ∧ TraceBefore X g b := by
  obtain ⟨g, hwg, hgs, hga⟩ := hI
  have hg1 : g.1 = a.1 := by rcases hga with h | ⟨rfl, -⟩ <;> [exact h.1; rfl]
  have hg2 : g.2 ≤ a.2 := by rcases hga with h | ⟨rfl, -⟩ <;> [exact h.2.1.le; exact le_rfl]
  have reach : ∀ (x : EvId), x.1 = a.1 → g.2 < x.2 → x.2 < (X.tr x.1).length →
      Relation.TransGen (DepStep L K X) (.thread w, true) (.thread x, false) :=
    fun x h1 h2 h3 => Relation.TransGen.tail' hwg (hgs.guard ⟨hg1.trans h1.symm, h2, h3⟩)
  rcases h with h | ⟨hs, key, i, j, hi, hj, hai, hjb, hb⟩ |
      ⟨x, w', m, rs, as, ⟨tx, count, pcx, hx⟩, ⟨⟨pcw, par, hw'⟩, hu⟩, -, hw1, hw2, hb, hx1, hx2⟩ |
      ⟨hs, i, j, ⟨phase, ha, hwo⟩, hil, hai, hjb, hb⟩ | ⟨i, j, hwb, hai, hjb, hb⟩ | h
  · refine ⟨g, hwg, hgs, ?_⟩
    rcases hga with h' | ⟨rfl, -⟩
    · exact h'.trans h.trace
    · exact h.trace
  · -- the arrival of `a`'s thread is counted by the release that the barrier return of `b`'s
    -- thread waits for
    obtain ⟨counti, pci, modei, hbarri⟩ := hi.2.1
    obtain ⟨countj, pcj, hbarj⟩ := hj.2.1
    have hlen : i < (X.tr a.1).length := len_of_get hbarri
    obtain ⟨key', hk', hdone⟩ :=
      ctaBarDone_of_ready hok.ready hbarj (show j + 1 < (X.tr b.1).length by omega)
    have hkey : key = key' := CtaBarK.key_unique hok.ctaBar hj hk'
    rw [← hkey] at hk' hdone
    obtain ⟨ic, hcomp⟩ := hdone
    have hwit : Witness L X (.thread (a.1, i)) (b.1, j) :=
      Witness.of_ctaBarCounted hk' hcomp hi hs.2.2
    exact ⟨(b.1, j), ((reach (a.1, i) rfl (by simp; omega) hlen).tail
      (DepStep.of_witness L hwit)).to_reflTransGen,
      .inr ⟨_, false, hbarj, by simp [Kind.resume]⟩, ⟨rfl, hjb, hb⟩⟩
  · -- the release arrival of `a` is a counter update that the poll `b` observed
    have hwob := hu
    obtain ⟨i, j, r, _, _, hri, hrid, -, -, -, -, -, -, -, -, -⟩ := hu
    have hpx : X.RefPresent (.thread x) := ⟨_, hx⟩
    have hgx : g.2 < x.2 := by
      rcases hga with h' | ⟨rfl, hna⟩
      · have := h'.2.1; omega
      · rcases Nat.lt_or_eq_of_le hx2 with h2 | h2
        · exact h2
        · exact (hna m tx count rs ⟨pcx, (Prod.ext hx1 h2.symm : x = g) ▸ hx⟩).elim
    have hwit : Witness L X (.thread x) w' := by
      have hmo : MbarObserved X r.id (.thread w') :=
        ⟨hrid.symm ▸ hpx, w', m, true, as, rfl, ⟨⟨pcw, par, hw'⟩, hrid.symm ▸ hwob⟩,
          fun r' hr' hid => arrive_counter ho hx hr' (hid.trans hrid)⟩
      have hmem : Need.node (· = r.id) ∈ pollNeeds X w' m :=
        List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hri, by
          simp only [needsIf, hmo, ite_true]
          exact List.mem_singleton.mpr rfl⟩
      refine ⟨(· = r.id), ?_, hrid.symm ▸ hpx, hrid.symm⟩
      rw [show Needs L X w' = pollNeeds X w' m by
        simp only [Needs, hw', KindNeeds, ite_true]]
      exact hmem
    exact ⟨w', ((reach x hx1 hgx (len_of_get hx)).tail
      (DepStep.of_witness L hwit)).to_reflTransGen, hg.wait hw', ⟨hw1, hw2, hb⟩⟩
  · -- the release arrival of the cluster phase is counted by the wait of `b`'s thread
    have hsz : L.clusterSizeOf (a.1 / L.block) =
        L.clusterSizeAt (L.clusterOfCta (b.1 / L.block)) := by
      simp only [Launch.clusterSizeOf, hs.2.2]
    have hcl : X.clusters (L.clusterOfCta (a.1 / L.block)) =
        X.clusters (L.clusterOfCta (b.1 / L.block)) := by rw [hs.2.2]
    have hsyn : ClusterBarrier.Synchronizes L.block
        (L.clusterSizeAt (L.clusterOfCta (b.1 / L.block)))
        (X.clusters (L.clusterOfCta (b.1 / L.block))) (a.1, i) (b.1, j) := by
      have h : ClusterBarrier.Synchronizes L.block (L.clusterSizeOf (a.1 / L.block))
          (X.clusters (L.clusterOfCta (a.1 / L.block))) (a.1, i) (b.1, j) := ⟨phase, ha, hwo⟩
      rwa [hsz, hcl] at h
    obtain ⟨i0, -, -, cta, warp, lanes, g, hi0, -, hmem, -, -⟩ := hwo
    rw [hs.2.2] at hi0
    have hclt : L.clusterOfCta (b.1 / L.block) < L.nclusters := by
      by_contra hcon
      rw [hok.cluster.2.1 _ (Nat.le_of_not_lt hcon)] at hi0
      exact absurd hi0 (by simp)
    obtain ⟨-, hsrc, -⟩ := hok.cluster.2.2 _ hclt
    obtain ⟨pcw, aligned, hwget⟩ :=
      (hsrc (.wait cta warp lanes) (List.mem_of_getElem? hi0) (g, (b.1, j)) hmem).2.2
    have hwit : Witness L X (.thread (a.1, i)) (b.1, j) :=
      Witness.of_clusterCounted hwget hsyn (present_of_len hil)
    exact ⟨(b.1, j), ((reach (a.1, i) rfl (by simp; omega) hil).tail
      (DepStep.of_witness L hwit)).to_reflTransGen,
      .inr ⟨_, false, hwget, by simp [Kind.resume]⟩, ⟨rfl, hjb, hb⟩⟩
  · -- the lane event of the instance `b`'s thread waits for is a witness of its return
    have hwit : Witness L X (.thread (a.1, i)) (b.1, j) :=
      Witness.of_warpBarEdge hok.warpBar hwb
    obtain ⟨-, mask, inst, ⟨pci, hi⟩, ⟨pcj, hj'⟩⟩ := hwb
    exact ⟨(b.1, j), ((reach (a.1, i) rfl (by simp; omega) (len_of_get hi)).tail
      (DepStep.of_witness L hwit)).to_reflTransGen,
      .inr ⟨_, true, hj', by simp [Kind.resume]⟩, ⟨rfl, hjb, hb⟩⟩
  · rcases h with h | h
    · exact ((hg.noMemSync _ _).1 h).elim
    · exact ((hg.noMemSync _ _).2 h).elim

/-- A `baseCausality` path from the return of a guard that is not a release arrival is a dependency
path. -/
theorem baseCausality_enables (hg : SyncGuarded L K X) (ho : AsyncCopy.ObjectsOk X)
    (hok : GuardOk L X) {w f : EvId} (hw : GuardSource K X w)
    (hna : ∀ m tx count sc, ¬ X.Arrive w m tx count true sc) (h : baseCausality L X w f) :
    Relation.TransGen (DepStep L K X) (.thread w, true) (.thread f, false) := by
  have key : ∀ {b}, baseCausality L X w b → ∃ g,
      Relation.ReflTransGen (DepStep L K X) (.thread w, true) (.thread g, true) ∧
        GuardSource K X g ∧ TraceBefore X g b := by
    intro b h
    induction h with
    | single h => exact guard_step hg ho hok ⟨w, .refl, hw, .inr ⟨rfl, hna⟩⟩ h
    | tail _ h ih =>
      obtain ⟨g, h1, h2, h3⟩ := ih
      exact guard_step hg ho hok ⟨g, h1, h2, .inl h3⟩ h
  obtain ⟨g, h1, h2, h3⟩ := key h
  exact Relation.TransGen.tail' h1 (h2.guard h3)

/-- A recorded asynchronous operation of an object is a counted update. -/
theorem async_counter (ho : AsyncCopy.ObjectsOk X) {m : Loc} {r : MBarrier.Record AsyncCopy.Ref}
    (hr : r ∈ X.objects m) {j : EvId} {q : AsyncCopy.Part} (hid : r.id = .async j q) :
    CounterUpdate r.action := by
  have h := ((ho m).2.1 r hr).1
  rw [hid] at h
  cases q <;> simp only [AsyncCopy.objectAction] at h
  all_goals (try cases h)
  all_goals
    generalize r.action = a at h ⊢
    repeat' (first | split at h | (simp only [bind, Option.bind] at h))
  all_goals (cases h; try simp [CounterUpdate])

/-- A notified tensor copy has written byte `(0, 0, 0)`: a valid descriptor has a nonempty box. -/
theorem tensor_write_present (hv : EffectValidity L X) {i : EvId} {o : TensorCopy.Observation}
    (ho : X.tensor i = some o) (hn : o.effects.notified = true) :
    ∃ x y k, X.AsyncPresent i (.write (.load x y k)) := by
  have hd := (hv.tensor i o ho).2.2.2
  have count_pos (axis : Fin (o.spec.outer + 1)) :
      0 < TensorTile.count o.spec.descriptor.box axis := by
    apply (TensorTile.index_lt_count_iff o.spec.descriptor.box axis
      (TensorDescriptor.effective_step_pos hd axis) 0).mpr
    simpa only [Nat.zero_mul] using (hd.2.2.2.2.1 axis).1
  have h0 := count_pos 0
  have h1 := TensorTile.rows_pos count_pos
  have hb := TensorDescriptor.format_bytes_pos o.spec.descriptor.format
  let slot : TensorTransfer.Slot o.spec.descriptor := ⟨⟨0, h0⟩, ⟨0, h1⟩, ⟨0, hb⟩⟩
  obtain ⟨v, hv'⟩ := (hv.tensor i o ho).2.1.complete hn slot
  exact ⟨0, 0, 0, o, slot, v, ho, by simp [TensorTransfer.slotAt, h0, h1, hb, slot], hv'⟩

/-- A wait observing an asynchronous notification observes it as a counter update. -/
theorem mbarObserved_of_waitObserves (ho : AsyncCopy.ObjectsOk X)
    {j : EvId} {q : AsyncCopy.Part} {w : EvId} {m : Loc} {acq : Bool} {ws : MbarScope}
    (hp : X.AsyncPresent j q) (h : AsyncCopy.WaitObserves X (.async j q) w m acq ws) :
    MbarObserved X (.async j q) (.thread w) :=
  ⟨hp, w, m, acq, ws, rfl, h, fun _ hr hid => async_counter ho hr hid⟩

end
end PTX

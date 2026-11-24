-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
public import Lemmas.Snoc.SnocObjectMemory
public import Lemmas.Snoc.SnocVisibility
public import Lemmas.Snoc.SnocOldCausality

@[expose] public section

section
/-! Issuing a TC operation adds its source event, not its asynchronous effects.
Existing snapshot effects retain their original issuing instructions and values. -/
namespace PTX.TcIssue
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

theorem snoc_memReads {pc : Nat} {k : TcKind} (he : e = ⟨pc, .tc k⟩)
    (ht : TmaOk X) {v : Ref} {a : Acc} {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads v a bs ↔ X.MemReads v a bs := by
  cases v with
  | thread i =>
    exact or_congr (snoc_kind_ne_iff (by rw [he]; simp))
      (exists_congr fun n => snoc_kind_ne_iff (by rw [he]; simp))
  | async i p =>
    have hcopy {s} : (X.snoc g e r).Copy i s ↔ X.Copy i s :=
      snoc_kind_iff (by rw [he]; simp)
    have htensor {address spec} :
        (X.snoc g e r).TensorIssue i address spec ↔ X.TensorIssue i address spec :=
      snoc_kind_iff (by rw [he]; simp)
    have hstore {address spec} :
        (X.snoc g e r).TensorStoreIssue i address spec ↔ X.TensorStoreIssue i address spec :=
      snoc_kind_iff (by rw [he]; simp)
    cases p <;> simp only [Execution.MemReads, snoc_async, hcopy, htensor, hstore,
      snoc_mmaRead_old ht.2.1]
    all_goals rfl

theorem snoc_tcK_noncollective (hc : isTcColl e = false) {i : EvId} {k : Nat} :
    (X.snoc g e r).TcK i k ↔ X.TcK i k := by
  constructor
  · intro hi
    rcases snoc_index_cases hi.lt with hold | hnew
    · exact (snoc_tcK_of_old hold).mp hi
    · subst i
      obtain ⟨⟨ev, hh, he⟩, _⟩ := hi
      rw [snoc_get_new] at hh
      cases hh
      rw [hc] at he
      cases he
  · intro hi
    exact (snoc_tcK_of_old hi.lt).mpr hi

end
end PTX.TcIssue
end

section
/-! The execution-order axioms after appending a `tcgen05` instruction that is no warp collective:
its only outgoing waiting edge is its own issue-to-completion step. -/
namespace PTX
open AsyncCopy
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0} {pc : Nat} {kind : TcKind}

/-- A `tcgen05` instruction that is no warp collective does not wait, so the appended one has not
returned. -/
theorem not_returned_new_of_noncollective (he : e = ⟨pc, .tc kind⟩) (hk : isTcColl e = false) :
    ¬ Returned (X.snoc g e r) (X.newId g) := by
  intro h
  unfold Returned at h
  rw [snoc_get_new] at h
  subst he
  cases kind <;> simp_all [isTcColl, Kind.resume, TcKind.resume]

/-- A `tcgen05` instruction that is no warp collective adds no outgoing dependency to another
event: it is no rendezvous, fills no need of another event, synchronizes with nothing and its
asynchronous stages are not yet present. -/
theorem snoc_noncollective_from_new (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (he : e = ⟨pc, .tc kind⟩) (hk : isTcColl e = false)
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.snoc g e r) (.thread (X.newId g), b) v) :
    b = false ∧ v = (.thread (X.newId g), true) := by
  have hord : e.kind.Ordinary := by rw [he]; trivial
  have hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok := by intros; rw [he]; simp
  have noBase : ∀ {f : EvId}, ¬ baseCausality L (X.snoc g e r) (X.newId g) f :=
    snoc_no_baseCausality_from_new_of_not_arrive (by intros; rw [he]; simp)
      (by intro _ _ h; rw [he] at h; cases h) (by intro _ _ _ h; rw [he] at h; cases h)
      (by intros; rw [he]; simp)
  have noOld : ¬ Waits L X (.thread (X.newId g), b) v := by
    intro hw
    obtain ⟨ev, he⟩ := (waits_present hX.effectValidity hw).1
    have hl := len_of_get he
    simp at hl
  rcases h with ⟨heq, hb, hb', _⟩ | ⟨_, _, i, j, hi, _, hij, hs, hl⟩ |
    ⟨i, j, hi, hj, hbar⟩ | ⟨_, _, i, j, hi, _, _, n, his, _⟩ |
    ⟨_, _, i, j, hi, _, _, k, hit, _⟩ | ⟨h1, h2, ha⟩ | ⟨h1, h2, m, ho⟩ |
    ⟨i, j, hi, hj, hcl⟩ | ⟨h1, h2, j, hj, hw⟩ | ⟨h1, h2, i, j, hi, hj, hw⟩ |
    ⟨h1, h2, i, j, hi, hj, hw⟩ | ⟨i, j, hi, hj, hw⟩ | ⟨h1, h2, i, j, hi, hj, cta, hp⟩ |
    ⟨h1, h2, i, j, hi, hj, hw⟩ | ⟨h1, h2, hi⟩
  · exact ⟨hb, Prod.ext heq.symm hb'⟩
  · cases hi
    rw [← hij, snoc_len, ite_eq_left rfl] at hl
    simp only at hs; omega
  · cases hi
    obtain ⟨ev, he⟩ := (ctaWaits_snoc_old hX.ctaBar hbar).1
    have hl := len_of_get he; simp at hl
  · cases hi
    have hl := ((snoc_shflK hns).mp his).1; simp at hl
  · cases hi
    have hl := ((TcIssue.snoc_tcK_noncollective hk).mp hit).lt; simp at hl
  · rcases ha with ⟨-, hb0, -⟩ | ⟨-, -, hs⟩
    · rw [h1] at hb0; cases hb0
    · simp [StageEdge] at hs
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2, m, ho⟩)))))))).elim
  · cases hi
    obtain ⟨ev, he⟩ := (clusterWaits_snoc_old hX.cluster hcl).1
    have hl := len_of_get he; simp at hl
  · rcases snoc_tc_witness hX hg (by rw [he]) hw with rfl | ⟨hc, -⟩
    · exact ⟨h1, Prod.ext hj h2⟩
    · rw [hk] at hc; cases hc
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1, h2, i, j, hi, hj, (snoc_warpWaits hord).mp hw⟩))))))))))).elim
  · cases hi
    exact (noBase (.single (.inr (.inr (.inr (.inr (.inr (.inl hw)))))))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨i, j, hi, hj, (snoc_regWaits hord).mp hw⟩))))))))))))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1, h2, i, j, hi, hj, cta, hp⟩)))))))))))))).elim
  · cases hi
    exact (noBase (.single (.inr (.inr (.inr (.inr (.inr (.inr hw)))))))).elim
  · obtain ⟨-, -, i, p, he, -, -, hap, -⟩ := hi
    have hl := refPresent_issuer_lt hX.effectValidity (f := .async _ p)
      ((TcIssue.snoc_asyncPresent hX.tma.2.1).mp hap)
    rw [← Ref.thread.inj he] at hl
    exact absurd hl (lt_irrefl _)

/-- Appending a noncollective tensor-core instruction is a sink frame for its two nodes. -/
theorem snoc_noncollective_sinkFrame (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (he : e = ⟨pc, .tc kind⟩) (hk : isTcColl e = false) :
    SinkFrame L K A X (X.snoc g e r) (fun x => x.1 = .thread (X.newId g)) :=
  snoc_sinkFrame_new hX (fun _ _ => (TcIssue.snoc_asyncPresent hX.tma.2.1).mp)
    (baseCausality_snocHistory_ordinary (records := X.objects) hX SnocRecords.same
      (by rw [he]; trivial))
    (fun _ _ h => snoc_noncollective_from_new hX hg he hk h)

end
end
end PTX
end

section
/-! A noncollective TC issue preserves existing memory effects. The order of the old
execution's conflicts at read bytes (`ReadsOrdered`, implied by its safety), proved by the
caller, transports memory constraints using preserved visibility, with no new order between old
accesses (`modelCausality_snoc_old_of`)
and the execution-order axioms of the append (guarded synchronization of the extension is a
hypothesis). Completion remains an independent extension obligation. -/
namespace PTX
noncomputable section

/-- A noncollective Tensor Core issue, when the conflicts at the bytes that are read are
ordered. -/
theorem consistent_tcissue_snoc_reads {L : Launch} {X : Execution} {g : Nat} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) {pc : Nat} {k : TcKind} (htc : e = ⟨pc, .tc k⟩)
    (hcoll : isTcColl e = false) (hord : ReadsOrdered L X) (hlast : LastReady L X g)
    (hextra : ExtensionObligations L A (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r))
    (htma : TmaOk (X.snoc g e r)) (hsg : SyncGuarded L K (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) :=
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f) :=
    baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf)
      (by intros; rw [htc]; simp) (by intros; rw [htc]; simp) (by intros; rw [htc]; simp)
      (by intros; rw [htc]; simp)
  consistent_snoc_collective_reads hX hord hg hrun hl he (by intros; rw [htc]; simp)
    (fun h => by subst htc; cases h) hlast
    (fun h => (not_returned_new_of_noncollective htc hcoll h).elim)
    (fun v a bs hv => (TcIssue.snoc_memReads htc hX.tma).mp hv)
    (fun v a bs => snoc_memWrites_control hX.effectValidity (by intros; rw [htc]; simp)
      (by intros; rw [htc]; simp))
    (fun _ _ _ hv => modelCausality_snoc_mono hX.tma.2.1 hv)
    (fun _ _ _ _ _ _ hv hf h => byteCausality_snoc_old_of hbo hX.effectValidity
      (refPresent_issuer_lt hX.effectValidity hv) (refPresent_issuer_lt hX.effectValidity hf) h)
    ((snoc_noncollective_sinkFrame hX hg htc hcoll).orderOk hX.orderOk)
    hsg hasm htma hextra

/-- A noncollective Tensor Core issue in a safe execution. -/
theorem consistent_tcissue_snoc {L : Launch} {X : Execution} {g : Nat} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) {pc : Nat} {k : TcKind} (htc : e = ⟨pc, .tc k⟩)
    (hcoll : isTcColl e = false) (hm : ¬ Mixed L X) (hr : ¬ Race L X)
    (hst : StrongOrdered L X) (hlast : LastReady L X g)
    (hextra : ExtensionObligations L A (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r))
    (htma : TmaOk (X.snoc g e r)) (hsg : SyncGuarded L K (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) :=
  consistent_tcissue_snoc_reads hX hg hrun hl he htc hcoll (.of_safe hm hr hst) hlast
    hextra hasm htma hsg

end
end PTX
end

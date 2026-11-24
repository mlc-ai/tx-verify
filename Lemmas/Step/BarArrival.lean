-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Issue
public import Lemmas.Snoc.SnocAsyncSilent

@[expose] public section

/-! # Appending a named-barrier arrival of either form

A proof tool. A released thread appends its next named-barrier arrival, `bar.sync` or
`bar.arrive` (`consistent_barArrival_snoc`, `barArrival_counted_extension`). The appended event
is the thread's last, so it needs no release: a `bar.sync` blocks until its generation is done
and a `bar.arrive` until its warp's arrival is recorded, which a later step supplies. The old
events keep their obligations: the thread's previous last event is released (`Released`), and
the new event adds no waiting edge out of an old one. -/

namespace PTX
open AsyncCopy
noncomputable section

/-- Appending a named-barrier arrival, of either form, keeps base causality among the old events:
the appended event is in no barrier history and writes nothing, so it synchronizes nothing old. -/
theorem baseCausality_snoc_old_barArrival {L : Launch} {X : Execution} {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (hcl : ClusterHistoryOk L X) (hbk : CtaBarHistoryOk L X)
    {id : Nat} {count : Option Nat} {mode : BarMode} (hk : e.kind = .bar id count mode)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length) :
    baseCausality L (X.snoc g e r) a b ↔ baseCausality L X a b :=
  ⟨fun h => baseCausality_old_of_step (fun hb => snoc_step_old_with_bar
    (fun _ _ he => by rw [hk] at he; cases he) hcl
    (.of_noWrite (fun _ _ he => by rw [hk] at he; cases he)
      (fun _ _ _ he => by rw [hk] at he; cases he))
    (fun _ _ => snoc_ctaBarK_history hbk) (fun _ _ => snoc_ctaBarArrivalK_history hbk)
    (fun _ _ _ _ he => by rw [hk] at he; cases he)
    (fun _ he => by rw [hk] at he; cases he) hb) h hbo, baseCausality_snoc⟩

/-- A thread's next named-barrier arrival, of either form, extends a consistent execution. -/
theorem consistent_barArrival_snoc {L : Launch} {X : Execution} {g : Nat} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    {id : Nat} {count : Option Nat} {mode : BarMode}
    (he : EStep K A L g t1 ⟨t1.pc, .bar id count mode⟩ o) (hlast : LastReady L X g)
    (hextra : ExtensionObligations L A (X.snoc g ⟨t1.pc, .bar id count mode⟩ (fun _ => none)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨t1.pc, .bar id count mode⟩ (fun _ => none))) :
    Consistent L K A mem0 (X.snoc g ⟨t1.pc, .bar id count mode⟩ (fun _ => none)) := by
  let ev : Event := ⟨t1.pc, .bar id count mode⟩
  let r : Nat → Option AsyncCopy.Ref := fun _ => none
  show Consistent L K A mem0 (X.snoc g ev r)
  have hs : ev.kind.AsyncSilent := trivial
  have hns : ∀ m a b c recv ok, ev.kind ≠ .shfl m a b c recv ok := by simp [ev]
  have hrmw : ∀ a old new, ev.kind ≠ .rmw a old new := by simp [ev]
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ev r) x f ↔ baseCausality L X x f) :=
    baseCausality_snoc_old_barArrival hX.cluster hX.ctaBar rfl
  have htma : TmaOk (X.snoc g ev r) :=
    hX.tmaOk_snoc_unobserved (by intro k h; cases h)
      fun _ => by simp only [objectAction, snoc_get_new, ev]
  have hnew : ¬ Returned (X.snoc g ev r) (X.newId g) := by
    unfold Returned
    rw [snoc_get_new]
    cases mode <;> simp [ev, Kind.resume, snoc_len]
  apply consistent_preserving_extension hX le_snoc
  · intro h hh
    by_cases hhg : h = g
    · subst hhg
      refine ⟨o, ?_⟩
      rw [snoc_tr, ite_eq_left rfl]; exact hrun.snoc hl he
    · rw [snoc_tr, ite_eq_right hhg]; exact hX.thr h hh
  · intro h hh
    rw [snoc_tr, ite_eq_right (by omega)]; exact hX.outside h hh
  · intro v a bs hv
    exact (Kind.AsyncSilent.snoc_memReads hs (by simp [ev]) hrmw).mp hv
  · intro v a bs hv
    exact (Kind.AsyncSilent.snoc_memWrites hs (by simp [ev]) hrmw).mp hv
  · intro v a bs hv
    exact (Kind.AsyncSilent.snoc_memWrites hs (by simp [ev]) hrmw).mpr hv
  · intro v a bs hv k
    have hold := (Kind.AsyncSilent.snoc_memReads hs (by simp [ev]) hrmw).mp hv
    exact (le_snoc (X := X) (g := g) (e := ev) (r := r)).2.1 v k ⟨a, bs, hold⟩
  · intro l x f hf
    exact Kind.AsyncSilent.modelCausality_snoc_old hs hbo
      (snoc_allocResultBefore_old hX.dependency.ready) (refPresent_issuer_lt hX.effectValidity hf)
  · exact ready_snocHistory (records := X.objects) hX SnocRecords.same (fun h => by cases h)
      hlast (fun h => (hnew h).elim)
  · exact snoc_shflOk hX.shfl hns
  · exact snoc_plain_orderOk hX
      (Kind.WaitFree.mk (by simp only [ev, Kind.Ordinary]) (fun _ h => by cases h)) hns
      (by simp [ev]) rfl rfl (by simp [ev]) (by simp [ev])
  · exact hasm
  · exact htma
  · rfl
  · exact hextra

namespace Step

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0} {g : Nat}

/-- **A released thread arrives on a named barrier**, by `bar.sync` or `bar.arrive`: a counted
extension. -/
theorem barArrival_counted_extension (hX : Consistent L K A mem0 X) {id : Nat}
    {count : Option Nat} {mode : BarMode} (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g)
    {t t1 : TState} {o : Option TState}
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨t1.pc, .bar id count mode⟩ (fun _ => none)))
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨t1.pc, .bar id count mode⟩ o) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ⟨t1.pc, .bar id count mode⟩ (fun _ => none)) x f ↔
        baseCausality L X x f) :=
    baseCausality_snoc_old_barArrival hX.cluster hX.ctaBar rfl
  have hY : Consistent L K A mem0 (X.snoc g ⟨t1.pc, .bar id count mode⟩ (fun _ => none)) :=
    consistent_barArrival_snoc hX hg hrun hl he hrel.ready
      (.snoc_quiet hX trivial hne nofun
        (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => by cases h)
        (readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo
          (fun _ _ _ _ h => by cases h))
        (hX.atomic.snoc hX.store hX.tma.1 nofun)
        (hX.fenceSc.snoc nofun fun _ _ hb h => (hbo hb).mp h)
        (hX.matrix.snoc rfl) (hX.reduce.snoc fun _ h => Kind.noConfusion h))
      hasm
  refine ⟨_, hY, le_snoc, ?_⟩
  rw [size_snoc hX hg rfl]
  omega

end Step

end
end PTX

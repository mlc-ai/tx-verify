-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Cluster.ClusterFirstPhase
public import Lemmas.Order.DependencyWitness
public import Core.Assembly.SharedLifetime

@[expose] public section

/-! # What a start cluster barrier with any arrival qualifier gives

A proof tool on top of `ClusterFirstPhase`, whose lemmas take a first cluster-barrier arrival of
any qualifier: `release` or `relaxed`, aligned or not. Let `first g` be the index of thread `g`'s
first cluster-barrier operation, an arrival, with its wait at `first g + 1`; before `first g` the
thread neither operates on the cluster barrier nor exits. A completed wait observes generation
zero, and every member of its cluster has recorded its first arrival in that generation
(`start_of_post_event`). A relaxed arrival does not synchronize memory
(`ClusterBarrier.Synchronizes` needs a release arrival); what the start barrier still gives is:

* **Publication of initializations** (OBJ-MBAR-INIT-PUBLICATION): an mbarrier initialization of `g0`
  followed in `g0` by `fence.mbarrier_init` before its first arrival is published to every event
  of a cluster member after its first wait (`init_fence_published_of_post`), through the
  restricted fence pattern, which allows a relaxed arrival.

A launch names the cluster-local index of a cluster member by its one-dimensional form, so these
lemmas ask for `L.OneDim`. -/

namespace PTX
noncomputable section

section FirstPhase

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {first : Nat → Nat}

/-- **The start barrier publishes the initializations fenced before the first arrival**: an
initialization of `m` (in the issuer's CTA's shared memory) at `a`, followed by
`fence.mbarrier_init` at `f < first g0`, is published to every event of a cluster member after its
first wait (OBJ-MBAR-INIT-PUBLICATION; the arrival may be relaxed). -/
theorem init_fence_published_of_post (hX : Consistent L K A mem0 X) (hblock : 0 < L.block)
    (hone : L.OneDim) {rel : Bool}
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (harrive : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc al, X.get (g, first g) = some ⟨pc, .cluster (.arrive rel al)⟩)
    (hwait : ∀ g < L.threads, first g + 1 < (X.tr g).length →
      ∃ pc al, X.get (g, first g + 1) = some ⟨pc, .cluster (.wait al)⟩)
    {g0 a f g j c pcf : Nat} {m : Loc} (hinit : X.MbInit (g0, a) m c)
    (hfence : X.get (g0, f) = some ⟨pcf, .fenceMbarInit⟩) (haf : a < f) (hf : f < first g0)
    (hsp : m.space = .shared) (hcta : m.cta = g0 / L.block)
    (hcluster : SameCluster L g0 g) {ev : Event} (he : X.get (g, j) = some ev)
    (hj : first g + 1 < j) :
    InitPublished L X (g0, a) (g, j) m := by
  obtain ⟨hw, ha, hhb⟩ :=
    start_of_post_event hX hblock hone hbefore harrive hwait hcluster he hj
  have hjlen : j < (X.tr g).length := len_of_get he
  obtain ⟨pca, al, harr_get⟩ := harrive g0 hcluster.1 (by
    obtain ⟨_, _, hap⟩ := hX.cluster.arrival_present ha
    exact len_of_get hap)
  obtain ⟨pcw, alw, hwait_get⟩ := hwait g hcluster.2.1 (by omega)
  exact .inr ⟨(g, first g + 1),
    ⟨c, (g0, f), (g0, first g0), pcf, pca, rel, al, pcw, alw, hinit,
     hsp, hcta, hfence, rfl, haf, rfl, hf, harr_get, hwait_get,
     ⟨L.clusterOfCta (g0 / L.block), 0, ha, hw⟩⟩, hhb⟩

/-- **A blocking event before the first arrival precedes, in the dependency order, every event of
a cluster member after its first wait**: the return of the blocking event precedes its thread's
arrival (`Resumes`), the arrival is a witness of the return of the member's wait (the wait's
`ClusterCounted` need, `Witness.of_clusterCounted`), and the wait's return precedes the event.

The old statement took `BlockingReturn L X (g0, s)`, the completed instance of the blocking
event; Core states the same fact as `Resumes K X (g0, s) (g0, first g0)` (a `TraceBefore` and a
blocking resume kind), whose edge is `DepStep.of_resumes`. -/
theorem lifetime_of_post (hX : Consistent L K A mem0 X) (hblock : 0 < L.block) (hone : L.OneDim)
    {rel : Bool}
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (harrive : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc al, X.get (g, first g) = some ⟨pc, .cluster (.arrive rel al)⟩)
    (hwait : ∀ g < L.threads, first g + 1 < (X.tr g).length →
      ∃ pc al, X.get (g, first g + 1) = some ⟨pc, .cluster (.wait al)⟩)
    {g0 s g j : Nat} (hcluster : SameCluster L g0 g)
    (hres : Resumes K X (g0, s) (g0, first g0)) {ev : Event} (he : X.get (g, j) = some ev)
    (hj : first g + 1 < j) :
    LifetimeOrder L K A X (.thread (g0, s), true) (.thread (g, j), false) := by
  obtain ⟨hw, ha, _⟩ := start_of_post_event hX hblock hone hbefore harrive hwait hcluster he hj
  obtain ⟨_, _, hapres⟩ := hX.cluster.arrival_present ha
  have hjlen : j < (X.tr g).length := len_of_get he
  obtain ⟨pcw, alw, hwait_get⟩ := hwait g hcluster.2.1 (by omega)
  rw [hcluster.2.2] at ha hw
  have hcounted : ClusterCounted L X (g, first g + 1) (g0, first g0) := .inl ⟨0, rel, hw, ha⟩
  obtain ⟨i, s', t', cta, warp, lanes, gg, hi, -, hmem, -, -⟩ := ha
  have hy : (g0, first g0) ∈ (X.clusters (L.clusterOfCta (g / L.block))).flatMap
      ClusterBarrier.Record.refs :=
    List.mem_flatMap.mpr
      ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(gg, (g0, first g0)), hmem, rfl⟩⟩
  have hneed : Need.node (· = .thread (g0, first g0)) ∈ Needs L X (g, first g + 1) := by
    simp only [Needs, hwait_get, KindNeeds, clusterNeeds, needsIf, List.mem_append,
      List.mem_flatMap]
    exact .inr ⟨_, List.mem_flatMap.mp hy, by simp [hcounted]⟩
  have h2 : DepStep L K X (.thread (g0, first g0), false) (.thread (g, first g + 1), true) :=
    DepStep.of_witness L (Witness.of_need L hneed ⟨_, hapres⟩ rfl)
  have hres3 : Resumes K X (g, first g + 1) (g, j) :=
    Resumes.of_blocking hwait_get (b := false) (by simp [Kind.resume]) ⟨rfl, hj, hjlen⟩
  have h3 : DepStep L K X (.thread (g, first g + 1), true) (.thread (g, j), false) :=
    DepStep.of_resumes L hres3
  have h1 : DepStep L K X (.thread (g0, s), true) (.thread (g0, first g0), false) :=
    DepStep.of_resumes L hres
  exact .inr ⟨.cluster 0, trivial,
    ((Relation.TransGen.single (.inl h1)).tail (.inl h2)).tail (.inl h3)⟩

end FirstPhase

/-- A shuffle is a blocking event, so its return precedes every later event of its thread
(`Resumes`, whose kind clause is automatic for a blocking kind). -/
theorem blockingReturn_of_shfl {K : Kernel} {X : Execution} {g s t pc : Nat} {m : ShflMode}
    {a : Value} {b c : Nat} {r : Value} {o : Bool}
    (he : X.get (g, s) = some ⟨pc, .shfl m a b c r o⟩) (hst : s < t)
    (hlt : t < (X.tr g).length) : Resumes K X (g, s) (g, t) :=
  Resumes.of_blocking he (b := true) (by simp [Kind.resume]) ⟨rfl, hst, hlt⟩

end
end PTX

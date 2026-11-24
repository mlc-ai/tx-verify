-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.ClusterStart
public import Kernels.FlashAttn4Fwd.Proof.Interface.Init
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Protocol.BarTable
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Flow.ElectActor
public import Lemmas.Flow.Elect

@[expose] public section

/-! # A table barrier's initialization is its first record

An object initialized by one event `e`, with count `c`, whose every other record is issued by
an event to which `e` is published (`InitPublished`: by causality, or by
`fence.mbarrier_init` and a cluster barrier, OBJ-MBAR-INIT-PUBLICATION), has `e`'s initialization as
its first record, without fault, and no other (`initFirst_of_published`, `InitFirst`): the published
initialization is not after the record in the object's history (`object_not_before_of_published`).

For the kernel's barrier table, barrier `b` of CTA `cta` (`init_first`):

* **Its other records are of its cluster, after the start** (`record_issuer`): every record but
  an initialization is a poll, an arrival, a copy's completion or a commit's arrival (no
  invalidation, bulk copy or cancellation request, `TmemFacts`), none of the prologue's kinds;
  its issuer is of the cluster when the barrier's users are (`Users`: the protocols' facts for
  threads and copies, `InitFacts.commit_cluster` for commits).
* **It is initialized** (`init_exists`): such an issuer passed the start cluster barrier, whose
  wait observed every arrival of the cluster, so each thread of the barrier's warp
  (`FBar.initWarp`) of `cta` reached its arrival. Lane 0 of the warp initialized the barrier
  before it, or an election before it returned another lane `l` (`InitFacts.init_done`); then
  the lane-`l` thread of the warp saw no election return another lane (elections of one warp
  with one mask agree, `ElectOk.deterministic`), so it initialized the barrier.
* **Once** (`init_unique`): an initialization of the barrier is by a thread of its warp of
  `cta`, with its count (`ClusterFacts.init_site`), by an elected lane, its thread's only one
  (`InitFacts.init`); two elected threads of one warp are one.
* **First**: every barrier initialization is fenced before the start cluster barrier, so it is
  published to every event of its cluster after the start (`ClusterStart.init_published`).

The protocols' premises follow (`ringInit`, `statsInit`, `outputInit`, `pReadyInit`,
`sFullInit`, `oFullInit`, `deallocInit`; each statement is the premise's definition). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.InitFirst
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An object initialized once, published to its other records, is initialized first.** -/
theorem initFirst_of_published (hX : Consistent L kernel asms mem0 X) {m : Loc} {e : EvId}
    {c : Nat} (hinit : X.MbInit e m c) (hcount : validCount c)
    (hsite : ∀ i pc n, X.get i = some ⟨pc, .mbInit m n⟩ → i = e ∧ n = c)
    (hpub : ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) → InitPublished L X e s.id.issuer m) :
    PairTmaRing.InitFirst X m c := by
  intro _ _
  obtain ⟨r0, h0, hid, ha, hf, -⟩ := init_record_success_of_unique_init hX hinit hcount
    (fun _ s _ hs ha => (BarTable.init_source_of_site hX hsite (List.mem_of_getElem? hs) ha).1)
    (fun _ s hs hnon => object_not_before_of_published hX ⟨c, hinit⟩
      (hpub s (List.mem_of_getElem? hs) hnon))
  refine ⟨r0, h0, ha, hf, fun q hq ⟨n, hqa⟩ => ?_⟩
  exact hX.record_eq hq (List.mem_of_getElem? h0)
    ((BarTable.init_source_of_site hX hsite hq hqa).1.trans hid.symm)

/-- Every table barrier's count is a valid arrival count. -/
theorem count_valid (b : FBar) : validCount b.count := by
  unfold validCount limit FBar.count
  split <;> omega

/-- **A table barrier initialized once is initialized first**, when its every other record is
issued by an event of its CTA's cluster after the start (not of the prologue's kinds, not
undefined behaviour). -/
theorem table_init_first (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) {b : FBar} {cta : Nat} {e : EvId} {pc : Nat}
    (hinit : X.get e = some ⟨pc, .mbInit (b.loc L cta) b.count⟩)
    (hsite : ∀ i pc n, X.get i = some ⟨pc, .mbInit (b.loc L cta) n⟩ → i = e)
    (hrec : ∀ s ∈ X.objects (b.loc L cta), (∀ n, s.action ≠ .init n) →
      ∃ ev, X.get s.id.issuer = some ev ∧ ¬ PreKind ev.kind ∧ (∀ f, ev.kind ≠ .ub f) ∧
        ctaOf L s.id.issuer.1 / 2 = cta / 2) :
    PairTmaRing.InitFirst X (b.loc L cta) b.count := by
  obtain ⟨g0, a⟩ := e
  have hg0 := Frame.lt_of_get hX hinit
  obtain ⟨b', hb', -, -⟩ := hc.init_site hg0 hinit
  have hcta : ctaOf L g0 = cta := (FBar.loc_inj hb').2.symm
  refine initFirst_of_published hX ⟨pc, hinit⟩ (count_valid b) (fun i pc' n hi => ?_) ?_
  · have he := hsite i pc' n hi
    subst he
    rw [hinit] at hi
    simp only [Option.some.injEq, Event.mk.injEq, Kind.mbInit.injEq, true_and] at hi
    exact ⟨rfl, hi.2.symm⟩
  · intro s hs hnon
    obtain ⟨ev, he, hk, hub, hcl⟩ := hrec s hs hnon
    generalize s.id.issuer = i at he hcl ⊢
    obtain ⟨g, j⟩ := i
    refine ClusterStart.init_published hpre hX hc hinit he hk hub ?_
    rw [clusterOf_eq hpre, clusterOf_eq hpre, hcta]
    exact hcl.symm

/-! ### The users of a barrier -/

/-- The users of object `m` are of its cluster: the threads that arrive on it or poll it, and
the threads that issue the copies completing on it. -/
structure Users (L : Launch) (X : Execution) (m : Loc) : Prop where
  arrive : ∀ {g j pc tx c : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, j) = some ⟨pc, .arrive m tx c rel sc⟩ → ctaOf L g / 2 = m.cta / 2
  wait : ∀ {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, j) = some ⟨pc, .wait m p ok acq sc⟩ → ctaOf L g / 2 = m.cta / 2
  tensor : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = m → ctaOf L i.1 / 2 = m.cta / 2

/-- **The records of an object with users of its cluster, other than initializations, are
issued after the start by events of the cluster.** -/
theorem record_issuer (hX : Consistent L kernel asms mem0 X) (htm : TmemFacts L X)
    (hi : InitFacts L X) {m : Loc} (hu : Users L X m) {s : Record Ref}
    (hs : s ∈ X.objects m) (hnon : ∀ n, s.action ≠ .init n) :
    ∃ ev, X.get s.id.issuer = some ev ∧ ¬ PreKind ev.kind ∧ (∀ f, ev.kind ≠ .ub f) ∧
      ctaOf L s.id.issuer.1 / 2 = m.cta / 2 := by
  cases record_source hX.tma.2.2.1 hs with
  | init _ _ ha => exact absurd ha (hnon _)
  | inval _ he _ => exact absurd he htm.no_inval
  | wait hid he _ =>
    exact ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp,
      by rw [hid]; exact hu.wait (Frame.lt_of_get hX he) he⟩
  | arrive hid he _ =>
    exact ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp,
      by rw [hid]; exact hu.arrive (Frame.lt_of_get hX he) he⟩
  | tensor hid he hm _ =>
    exact ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp,
      by rw [hid]; exact hu.tensor he hm⟩
  | increment _ he _ => exact absurd he htm.no_arriveOn
  | arriveOn _ he _ _ _ => exact absurd he htm.no_arriveOn
  | bulk _ he _ _ _ => exact absurd he htm.no_bulk
  | commit hid he ht _ =>
    exact ⟨_, by rw [hid]; exact he, by simp [PreKind], by simp,
      by rw [hid]; exact (hi.commit_cluster he ht).symm⟩
  | clc _ he _ _ _ => exact absurd he htm.no_clc

/-! ### Initialized once, by the barrier's warp -/

/-- An initialization of barrier `b` of CTA `cta` is by a thread of `b`'s warp of `cta`, with
`b`'s count. -/
theorem init_of_site (hc : ClusterFacts L X) {g k pc n cta : Nat} {b : FBar} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .mbInit (b.loc L cta) n⟩) :
    warpOf L g = b.initWarp ∧ ctaOf L g = cta ∧ n = b.count := by
  obtain ⟨b', hm, hn, h12, h0⟩ := hc.init_site hg he
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hm
  refine ⟨?_, rfl, hn⟩
  unfold FBar.initWarp
  split_ifs with hd
  · exact h12 hd
  · exact h0 hd

/-- **A table barrier is initialized once.** -/
theorem init_unique (hX : Consistent L kernel asms mem0 X) (hc : ClusterFacts L X)
    (hi : InitFacts L X) {b : FBar} {cta : Nat} {e i : EvId} {pc pc' n n' : Nat}
    (he : X.get e = some ⟨pc, .mbInit (b.loc L cta) n⟩)
    (hi' : X.get i = some ⟨pc', .mbInit (b.loc L cta) n'⟩) : i = e := by
  obtain ⟨g1, k1⟩ := e
  obtain ⟨g2, k2⟩ := i
  have hg1 := Frame.lt_of_get hX he
  have hg2 := Frame.lt_of_get hX hi'
  obtain ⟨hw1, hc1, -⟩ := init_of_site hc hg1 he
  obtain ⟨hw2, hc2, -⟩ := init_of_site hc hg2 hi'
  obtain ⟨⟨j1, -, q1, inst1, he1⟩, hu1⟩ := hi.init hg1 he
  obtain ⟨⟨j2, -, q2, inst2, he2⟩, -⟩ := hi.init hg2 hi'
  have hgg : g2 = g1 := selected_elect_thread_unique hX.elect he2 he1
    ⟨⟨hg2, hg1, show ctaOf L g2 = ctaOf L g1 by omega⟩,
      show warpOf L g2 = warpOf L g1 by omega⟩ rfl rfl
  subst hgg
  rw [hu1 _ _ _ hi']

/-! ### Initialized before its users -/

/-- Thread `h` of the cluster of an event after the start reached its cluster arrival. -/
theorem reach (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) {g j : Nat} {ev : Event} (he : X.get (g, j) = some ev)
    (hk : ¬ PreKind ev.kind) (hub : ∀ f, ev.kind ≠ .ub f) {h : Nat} (hh : h < L.threads)
    (hcl : ctaOf L h / 2 = ctaOf L g / 2) : clFirst X h < (X.tr h).length := by
  have hb : 0 < L.block := by rw [hpre.block]; decide
  have hg := Frame.lt_of_get hX he
  have hsc : SameCluster L h g := by
    refine ⟨hh, hg, ?_⟩
    simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]
    exact hcl
  obtain ⟨-, ha, -⟩ := start_of_post_event hX hb hpre.oneDimLaunch.1 (ClusterStart.before hc)
    (ClusterStart.arrive' hc) (ClusterStart.wait' hc) hsc he (hc.post hg he hk hub)
  obtain ⟨_, _, hapres⟩ := hX.cluster.arrival_present ha
  exact len_of_get hapres

theorem initWarp_le (b : FBar) : b.initWarp ≤ 12 := by
  unfold FBar.initWarp
  split_ifs <;> omega

/-- **A table barrier with a user after the start is initialized.** -/
theorem init_exists (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (hi : InitFacts L X) (b : FBar) {cta g j : Nat}
    {ev : Event} (he : X.get (g, j) = some ev) (hk : ¬ PreKind ev.kind)
    (hub : ∀ f, ev.kind ≠ .ub f) (hcl : ctaOf L g / 2 = cta / 2) :
    ∃ e pc n, X.get e = some ⟨pc, .mbInit (b.loc L cta) n⟩ := by
  have hblk := hpre.block
  have hg := Frame.lt_of_get hX he
  have hcg := cta_lt hg
  have hgr := hpre.grid
  have hwb := initWarp_le b
  have hcta : cta < L.grid := by omega
  have h0 : cta * L.block + 32 * b.initWarp < L.threads := by
    simp only [Launch.threads]
    rw [hblk] at ⊢
    nlinarith
  have hc0 : ctaOf L (cta * L.block + 32 * b.initWarp) = cta := by
    simp only [ctaOf, hblk]
    omega
  have hw0 : warpOf L (cta * L.block + 32 * b.initWarp) = b.initWarp := by
    simp only [warpOf, hblk]
    omega
  have hr0 := reach hpre hX hc he hk hub h0 (by rw [hc0]; omega)
  rcases hi.init_done h0 hr0 with hd | ⟨k, -, pc, inst, l, hel, hl⟩
  · obtain ⟨k, -, pc, n, hk⟩ := hd b hw0.symm
    rw [hc0] at hk
    exact ⟨_, pc, n, hk⟩
  · -- the leader lane of the warp reached its cluster arrival too; a full-mask election of the
    -- warp returns the same leader in every lane, so the leader lane did not elect another lane
    have hl32 : l < 32 := (hX.elect.1 _ _ _ _ _ hel).2.2.1
    have hh : cta * L.block + 32 * b.initWarp + l < L.threads := by
      simp only [Launch.threads]
      rw [hblk] at ⊢
      nlinarith
    have hch : ctaOf L (cta * L.block + 32 * b.initWarp + l) = cta := by
      simp only [ctaOf, hblk]
      omega
    have hwh : warpOf L (cta * L.block + 32 * b.initWarp + l) = b.initWarp := by
      simp only [warpOf, hblk]
      omega
    have hrh := reach hpre hX hc he hk hub hh (by rw [hch]; omega)
    rcases hi.init_done hh hrh with hd | ⟨k', -, pc', inst', l', hel', hl'⟩
    · obtain ⟨k, -, pc, n, hk⟩ := hd b hwh.symm
      rw [hch] at hk
      exact ⟨_, pc, n, hk⟩
    · have hsw : SameWarp L (cta * L.block + 32 * b.initWarp)
          (cta * L.block + 32 * b.initWarp + l) :=
        ⟨⟨h0, hh, by rw [hblk]; omega⟩, by rw [hblk]; omega⟩
      have hll := hX.elect.2.2 _ _ _ _ _ _ _ _ _ hel hel' hsw
      refine absurd ?_ hl'
      rw [← hll]
      simp only [laneOf, hblk]
      omega

/-! ### Initialized first -/

/-- **A table barrier whose users are of its cluster is initialized first, once, without fault,
with its count.** -/
theorem init_first (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (b : FBar) (cta : Nat)
    (hu : Users L X (b.loc L cta)) : PairTmaRing.InitFirst X (b.loc L cta) b.count := by
  intro r hr
  obtain ⟨e, pc, n, he⟩ : ∃ e pc n, X.get e = some ⟨pc, .mbInit (b.loc L cta) n⟩ := by
    by_cases hnon : ∃ n, r.action = .init n
    · obtain ⟨n, ha⟩ := hnon
      cases record_source hX.tma.2.2.1 hr with
      | init _ he _ => exact ⟨_, _, _, he⟩
      | increment _ he _ => exact absurd he htm.no_arriveOn
      | arriveOn _ he _ _ _ => exact absurd he htm.no_arriveOn
      | bulk _ he _ _ _ => exact absurd he htm.no_bulk
      | _ => simp_all
    · obtain ⟨ev, hev, hk, hub, hcl⟩ :=
        record_issuer hX htm hi hu hr (fun n h => hnon ⟨n, h⟩)
      exact init_exists hpre hX hc hi b hev hk hub hcl
  obtain ⟨-, -, rfl⟩ := init_of_site hc (Frame.lt_of_get hX he) he
  exact table_init_first hpre hX hc he (fun i pc' n' hi' => init_unique hX hc hi he hi')
    (fun s hs hnon => record_issuer hX htm hi hu hs hnon) r hr

/-! ### The protocols' barriers -/

theorem count_ring {b : FBar} (h : b.ring) : b.count = 1 := by
  cases b <;> simp_all [FBar.ring, FBar.count]

/-- The users of a ring barrier are of its cluster. -/
theorem ring_users (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X) {b : FBar}
    (hb : b.ring) (cta : Nat) : Users L X (b.loc L cta) where
  arrive hg he := by
    obtain ⟨-, rfl, -⟩ := ht.arrive hg he hb
    rfl
  wait hg he := by
    obtain ⟨rfl, -⟩ := ht.poll hg he hb
    rfl
  tensor he hm := by
    obtain ⟨-, hc, -⟩ := ht.issue (Frame.lt_of_get hX he) he hm hb
    show ctaOf L _ / 2 = cta / 2
    rw [hc, pairBase]
    omega

/-- **`RingInit`**: every ring barrier is initialized first, once, with count one. -/
theorem ringInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (ht : RingFacts L X) :
    ∀ cta (b : FBar), b.ring → PairTmaRing.InitFirst X (b.loc L cta) 1 := by
  intro cta b hb
  rw [← count_ring hb]
  exact init_first hpre hX hc htm hi b cta (ring_users hX ht hb cta)

/-- **`StatsInit`**: every credit barrier is initialized first, once, with count 128. -/
theorem statsInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hs : StatsFacts L X) :
    ∀ c st, st < 2 → PairTmaRing.InitFirst X (statsBar L c st) 128 := by
  intro c st hst
  refine init_first hpre hX hc htm hi (.stats ⟨st, hst⟩) c ⟨fun hg he => ?_, fun hg he => ?_,
    fun he hm => absurd hm (hs.credit_tensor hst he)⟩
  · obtain ⟨-, -, rfl, -⟩ := hs.credit_arrive hg hst he
    rfl
  · obtain ⟨-, -, rfl, -⟩ := hs.credit_poll hg hst he
    rfl

/-- **`OutputInit`**: every staged barrier (count 128) and free barrier (count 32) is
initialized first, once. -/
theorem outputInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (ho : OutputFacts L X) :
    ∀ c st, st < 2 → PairTmaRing.InitFirst X (stagedBar L c st) 128 ∧
      PairTmaRing.InitFirst X (freeBar L c st) 32 := by
  intro c st hst
  refine ⟨init_first hpre hX hc htm hi (.oStaged ⟨st, hst⟩) c ⟨fun hg he => ?_,
    fun hg he => ?_, fun he hm => absurd hm (ho.stage_tensor hst he).1⟩,
    init_first hpre hX hc htm hi (.oFree ⟨st, hst⟩) c ⟨fun hg he => ?_, fun hg he => ?_,
    fun he hm => absurd hm (ho.stage_tensor hst he).2⟩⟩
  · obtain ⟨-, -, rfl, -⟩ := ho.staged_arrive hg hst he
    rfl
  · obtain ⟨-, rfl, -⟩ := ho.staged_poll hg hst he
    rfl
  · obtain ⟨-, rfl, -⟩ := ho.free_arrive hg hst he
    rfl
  · obtain ⟨-, -, rfl, -⟩ := ho.free_poll hg hst he
    rfl

/-- **`PReadyInit`**: every P-ready object is initialized first, once, with count 512. -/
theorem pReadyInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hp : PReadyFacts L X) :
    ∀ c st, leadCta c = c → st < 2 → PairTmaRing.InitFirst X (pReadyBar L c st) 512 := by
  intro c st _ hst
  refine init_first hpre hX hc htm hi (.pReady ⟨st, hst⟩) c ⟨fun hg he => ?_, fun hg he => ?_,
    fun he hm => absurd hm (hp.p_tensor hst he)⟩
  · obtain ⟨hl, -⟩ := hp.p_arrive hg hst he
    show _ = c / 2
    rw [← hl, leadCta]
    omega
  · obtain ⟨rfl, -⟩ := hp.p_poll hg hst he
    rfl

/-- **`SFullInit`**: every S-full object is initialized first, once, with count one. -/
theorem sFullInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hs : SFullFacts L X) :
    ∀ c st, st < 2 → PairTmaRing.InitFirst X (sFullBar L c st) 1 := by
  intro c st hst
  refine init_first hpre hX hc htm hi (.sFull ⟨st, hst⟩) c ⟨fun _ he => absurd he
    (hs.s_arrive hst), fun hg he => ?_, fun he hm => absurd hm (hs.s_tensor hst he)⟩
  obtain ⟨rfl, -⟩ := hs.s_poll hg hst he
  rfl

/-- **`OFullInit`**: every O-full object is initialized first, once, with count one. -/
theorem oFullInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (ho : OFullFacts L X) :
    ∀ c st, st < 2 → PairTmaRing.InitFirst X (oFullBar L c st) 1 := by
  intro c st hst
  refine init_first hpre hX hc htm hi (.oFull ⟨st, hst⟩) c ⟨fun _ he => absurd he
    (ho.o_arrive hst), fun hg he => ?_, fun he hm => absurd hm (ho.o_tensor hst he)⟩
  obtain ⟨rfl, -⟩ := ho.o_poll hg hst he
  rfl

/-- The handshake barrier's users are of its cluster. -/
theorem dealloc_users (htm : TmemFacts L X) (cta : Nat) : Users L X (FBar.loc L cta .dealloc) where
  arrive hg he := by
    obtain ⟨-, hp, -⟩ := htm.hs_arrive hg he rfl
    show _ = cta / 2
    rw [hp, pairCta]
    omega
  wait hg he := by
    obtain ⟨-, rfl, -⟩ := htm.hs_wait hg he rfl
    rfl
  tensor he hm := absurd hm (htm.hs_tensor he)

/-- **The handshake barrier is initialized first, once, with count 32.** -/
theorem deallocInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (cta : Nat) :
    PairTmaRing.InitFirst X (FBar.loc L cta .dealloc) 32 :=
  init_first hpre hX hc htm hi .dealloc cta (dealloc_users htm cta)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.InitFirst

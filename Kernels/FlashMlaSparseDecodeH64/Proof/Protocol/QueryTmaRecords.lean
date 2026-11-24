-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingObjects
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualMbarInit
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxActualArrivals
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitOrigins
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents

@[expose] public section

/-! # Actual records on the query TMA completion object -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat}

/-- The CTA-local object tracking the query's eight tensor transfers. -/
abbrev object (L : Launch) (cta : Nat) : Loc :=
  ⟨.shared, cta, L.sharedBase + 222776⟩

abbrev Sound (P : Params) (L : Launch) : Prop :=
  ∀ g < L.threads, (Machine.machine P L g).Sound

/-- An issue completing on the query object is a real query-load site with its exact tile. -/
theorem actual_issue_source {g i a : Nat} {e : Event} {sp : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .tensorIssue a sp)
    (hm : sp.mbar = object L cta) :
    ctaOf L g = cta ∧ ∃ q tile,
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qLoad tile ∧ sp = MmaDataTrace.queryTmaSpec P L g tile := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_at_followed hX (hs g hg).machine
    (actual_tensor_issue_followed hpre hX hs he hk) he
    (by intro f h; rw [hk] at h; cases h)
  have hsite := RingTensorEvents.issue_site hf hk
  cases d
  case mma q =>
    obtain ⟨tile, hq⟩ := hsite
    have hspec := (QueryTmaSites.fired_load hpre hg hq hf hk).2
    have hcta := congrArg Loc.cta hm
    rw [hspec] at hcta
    exact ⟨hcta, q, tile, hd, hq, hspec⟩
  case tma q =>
    obtain ⟨tile, hq⟩ := hsite
    have hraw := (TmaGatherCounts.gather_event_fields hpre hq hf hk).2.2.1
    have haddr := congrArg Loc.addr (hm.symm.trans hraw)
    change L.sharedBase + 222776 = L.sharedBase + (222808 + 8 * (q.block % 2)) at haddr
    omega
  all_goals exact hsite.elim

/-- A query complete-tx record names an actual tile issue and accounts for 8192 bytes. -/
theorem actual_completion_source {r : Record Ref} {n : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hr : r ∈ X.objects (object L cta)) (ha : r.action = .completeTx n) :
    n = 8192 ∧ ∃ g i e a sp q tile, r.id = .async (g, i) (.notify .load) ∧
      X.get (g, i) = some e ∧ e.kind = .tensorIssue a sp ∧ ctaOf L g = cta ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qLoad tile ∧ sp = MmaDataTrace.queryTmaSpec P L g tile := by
  obtain ⟨⟨g, i⟩, e, a, sp, hId, he, hk, hm, hb⟩ := object_completion_source hX hr ha
  obtain ⟨hc, q, tile, hd, hsite, hspec⟩ := actual_issue_source hpre hX hs he hk hm
  have hshape := Result.queryTile_shape P L g tile
  rw [hspec, TensorTransfer.bytes, hshape.1, hshape.2.1, hshape.2.2] at hb
  exact ⟨hb.symm, g, i, e, a, sp, q, tile, hId, he, hk, hc, hd, hsite, hspec⟩

private theorem arrival_source {g i tx count : Nat} {e : Event} {rel : Bool} {sc : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (object L cta) tx count rel sc) :
    count = 1 ∧ tx = 65536 ∧ ctaOf L g = cta ∧ ∃ q,
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧ q.site = .qArrive := by
  have hFollow : Frame.stateAt (Machine.code P L) X g i ≠ some none := by
    intro hDismiss
    have hRange := dismissed_arrival_range hpre hX hs he hk hDismiss
    change L.sharedBase + 222872 ≤ L.sharedBase + 222776 ∧ _ at hRange
    omega
  obtain ⟨d, _, hstate, hf⟩ :=
    RingSourceSites.fired_at_followed hX (hs g (Frame.lt_of_get hX he)).machine hFollow he
      (by intro f h; rw [hk] at h; cases h)
  have hsite := RingSourceSites.arrive_site hf hk
  have apart {loc : Loc} {bytes n : Nat} {release : Bool} {scope : MbarScope}
      (h : e.kind = .arrive loc bytes n release scope) : loc.addr = L.sharedBase + 222776 :=
    congrArg Loc.addr (Kind.arrive.inj (h.symm.trans hk)).1
  cases d
  case wg0 d =>
    rcases hsite with hd | hd | hd
    · have h := apart (RingEvents.lastStore_arrive hpre hd hf)
      change L.sharedBase + 222768 = L.sharedBase + 222776 at h
      omega
    · have h := apart (RingEvents.maskFree_arrive hpre hd hf)
      change L.sharedBase + (222872 + 8 * (d.block % 4)) = L.sharedBase + 222776 at h
      omega
    · have h := apart (RingEvents.scores_arrive hpre hd hf)
      change L.sharedBase + (222920 + 8 * (d.block % 2)) = L.sharedBase + 222776 at h
      omega
  case mma d =>
    have h := Kind.arrive.inj (hk.symm.trans (RingEvents.query_expectTx hpre hsite hf))
    exact ⟨h.2.2.1, h.2.1, (congrArg Loc.cta h.1).symm, d, hstate, hsite⟩
  case tma d =>
    rcases hsite with hd | hd
    · have h := apart (RingEvents.rawReady_expectTx hpre hd hf)
      change L.sharedBase + (222808 + 8 * (d.block % 2)) = L.sharedBase + 222776 at h
      omega
    · have h := apart (RingEvents.validFree_arrive hpre hd hf)
      change L.sharedBase + (222872 + 8 * (d.block % 4)) = L.sharedBase + 222776 at h
      omega
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    have h := apart (RingEvents.validReady_arrive hpre hd hf)
    change L.sharedBase + (222840 + 8 * (d.block % 4)) = L.sharedBase + 222776 at h
    omega
  case wg2 d =>
    rcases hsite with hd | hd
    · have h := apart (RingEvents.dequantReady_arrive hpre hd hf)
      change L.sharedBase + (222792 + 8 * (d.block % 2)) = L.sharedBase + 222776 at h
      omega
    · have h := apart (RingEvents.rawFree_arrive hpre hd hf)
      change L.sharedBase + (222824 + 8 * (d.block % 2)) = L.sharedBase + 222776 at h
      omega
  all_goals exact hsite.elim

private theorem no_commit {id : EvId} {tag : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get id = some ⟨tag, .tc (.commit sp)⟩)
    (hrank : TcCommit.target sp rank = some (object L cta)) : False := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hst, hf⟩ := actual_commit_fired hpre hX hs he rfl
  obtain ⟨_, q, rfl, ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, hm⟩⟩ :=
    RingCommitEvents.commit_source hpre hg hf rfl hrank
  · have ho := congrArg Loc.addr hm
    change L.sharedBase + 222776 = L.sharedBase + 222784 at ho
    omega
  · have ho := congrArg Loc.addr hm
    change L.sharedBase + 222776 = L.sharedBase + (222904 + 8 * (q.i % 2)) at ho
    omega
  · have ho := congrArg Loc.addr hm
    change L.sharedBase + 222776 = L.sharedBase + (222936 + 8 * (q.i % 2)) at ho
    omega

/-- An arrival on the query object is the elected MMA lane's expect-tx for all eight tiles. -/
theorem actual_arrival_record {r : Record Ref} {n tx : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hr : r ∈ X.objects (object L cta)) (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 65536 ∧ ∃ g i e q, r.id = .thread (g, i) ∧
      X.get (g, i) = some e ∧ ctaOf L g = cta ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧ q.site = .qArrive := by
  cases record_source hX.tma.2.2.1 hr with
  | arrive hid he hact =>
    obtain ⟨rfl, rfl⟩ := Action.arrive.inj (ha.symm.trans hact)
    obtain ⟨hn, htx, hc, q, hstate, hsite⟩ := arrival_source hpre hX hs he rfl
    exact ⟨hn, htx, _, _, _, q, hid, he, hc, hstate, hsite⟩
  | commit _ he htarg _ => exact (no_commit hpre hX hs he htarg).elim
  | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | init _ _ h | inval _ _ h | wait _ _ h | increment _ _ h
  | tensor _ _ _ h | bulk _ _ _ _ h | clc _ _ _ _ h =>
    rw [ha] at h
    cases h

/-- The first query-object record is its published one-arrival initialization. -/
theorem actual_init_first
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    PairTmaRing.InitFirst X (object L cta) 1 := by
  let j : Fin 23 := 1
  obtain ⟨init, hInit⟩ := actual_init_sites hpre hX hs
  change PairTmaRing.InitFirst X (IndexRing.initTable.loc L cta j) (initCount j)
  apply IndexRing.published_init_first hX hInit cta j
  intro r hr hNotInit
  have after_init {g i : Nat} {q : Wg1Mma.D} {e : Event}
      (he : X.get (g, i) = some e) (hc : ctaOf L g = cta)
      (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma q))) :
      ∃ a, X.MbInit a (IndexRing.initTable.loc L cta j) (initCount j) ∧
        baseCausality L X a (g, i) := by
    obtain ⟨a, hMb, hBefore⟩ := completed_init_before_followed_role hpre hX hs he hState
      (by intro s h; cases h) j
    rw [hc] at hMb
    exact ⟨a, hMb, hBefore⟩
  have use_before :
      ∃ a, X.MbInit a (IndexRing.initTable.loc L cta j) (initCount j) ∧
        baseCausality L X a r.id.issuer := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact (hNotInit _ ha).elim
    | @wait g i _ _ _ _ _ hid he _ =>
      obtain ⟨hc, a, hMb, hOrder⟩ := table_init_before_actual_poll hpre hX hs he rfl j
      change cta = ctaOf L g at hc
      rw [← hc] at hMb
      rw [hid]
      exact ⟨a, hMb, hOrder⟩
    | arrive hid he _ =>
      obtain ⟨_, _, hc, q, hState, _⟩ := arrival_source hpre hX hs he rfl
      rw [hid]
      exact after_init he hc hState
    | @commit id _ _ _ hid he htarget _ =>
      exact (no_commit hpre hX hs he htarget).elim
    | inval _ _ hAct => exact ((objects_single_lifetime hX _) r hr hAct).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
    | tensor _ _ _ hAct | bulk _ _ _ _ hAct | clc _ _ _ _ hAct =>
      obtain ⟨_, g, i, e, _, _, q, _, hid, he, _, hc, hState, _, _⟩ :=
        actual_completion_source hpre hX hs hr hAct
      rw [hid]
      exact after_init he hc hState
  obtain ⟨a, hMb, hBefore⟩ := use_before
  have ha := (hInit j cta a _ _ trivial hMb.choose_spec).1
  rw [← ha]
  exact ⟨hMb, .inl hBefore⟩

/-- The actual query TMA history applies to the tracked interface. -/
theorem issue_source {g i a : Nat} {e : Event} {sp : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : Sound P L) (_ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hk : e.kind = .tensorIssue a sp)
    (hm : sp.mbar = object L cta) :
    ctaOf L g = cta ∧ ∃ q tile,
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qLoad tile ∧ sp = MmaDataTrace.queryTmaSpec P L g tile :=
  actual_issue_source hpre hX (fun _ hg => Machine.code_sound hpre hg) he hk hm

/-- The actual query TMA history applies to the tracked interface. -/
theorem completion_source {r : Record Ref} {n : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : Sound P L) (_ht : Frame.Tracked (Machine.code P L) X)
    (hr : r ∈ X.objects (object L cta)) (ha : r.action = .completeTx n) :
    n = 8192 ∧ ∃ g i e a sp q tile, r.id = .async (g, i) (.notify .load) ∧
      X.get (g, i) = some e ∧ e.kind = .tensorIssue a sp ∧ ctaOf L g = cta ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qLoad tile ∧ sp = MmaDataTrace.queryTmaSpec P L g tile :=
  actual_completion_source hpre hX (fun _ hg => Machine.code_sound hpre hg) hr ha

/-- The actual query TMA history applies to the tracked interface. -/
theorem arrival_record {r : Record Ref} {n tx : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : Sound P L) (_ht : Frame.Tracked (Machine.code P L) X)
    (hr : r ∈ X.objects (object L cta)) (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 65536 ∧ ∃ g i e q, r.id = .thread (g, i) ∧
      X.get (g, i) = some e ∧ ctaOf L g = cta ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧ q.site = .qArrive :=
  actual_arrival_record hpre hX (fun _ hg => Machine.code_sound hpre hg) hr ha

/-- The actual query TMA history applies to the tracked interface. -/
theorem init_first
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : Sound P L) (_ht : Frame.Tracked (Machine.code P L) X) :
    PairTmaRing.InitFirst X (object L cta) 1 :=
  actual_init_first hpre hX (fun _ hg => Machine.code_sound hpre hg)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords

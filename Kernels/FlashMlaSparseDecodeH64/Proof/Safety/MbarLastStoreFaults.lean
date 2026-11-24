-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarSimpleFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingInit
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingObjects
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.MbarRingBlocker

public section

/-! # Fault-free publication of the last output store -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat}

private abbrev lastStore (L : Launch) (cta : Nat) : Loc :=
  ⟨.shared, cta, L.sharedBase + 222768⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem last_store_source {g i tx count : Nat} {rel : Bool} {sc : MbarScope} {e : Event}
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (lastStore L cta) tx count rel sc) :
    count = 1 ∧ tx = 0 ∧ ctaOf L g = cta ∧ tidOf L g < 128 ∧
      ∃ d : Wg0.D, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
        d.site = .lastStore ∧ d.sub = 0 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hState, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by
      intro f hf
      rw [hk] at hf
      cases hf)
  have hsite := RingSourceSites.arrive_site hf hk
  have apart {loc : Loc} {bytes n : Nat} {release : Bool} {scope : MbarScope}
      (h : e.kind = .arrive loc bytes n release scope) : loc.addr = L.sharedBase + 222768 :=
    (congrArg Loc.addr (Kind.arrive.inj (h.symm.trans hk)).1)
  cases d
  case wg0 d =>
    rcases hsite with hd | hd | hd
    · have hFields := Kind.arrive.inj (hk.symm.trans (RingEvents.lastStore_arrive hpre hd hf))
      have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      have hTid : tidOf L g < 128 := by simp only [wgOf] at hWg; omega
      have hi : Wg0.Inv P L g d := hf.choose_spec.1.2
      have hSub : d.sub = 0 := by simpa [hd, Wg0.Site.elems] using hi.subLt
      exact ⟨hFields.2.2.1, hFields.2.1, (congrArg Loc.cta hFields.1).symm,
        hTid, d, hState, hd, hSub⟩
    · have h := apart (RingEvents.maskFree_arrive hpre hd hf)
      change L.sharedBase + (222872 + 8 * (d.block % 4)) = L.sharedBase + 222768 at h
      omega
    · have h := apart (RingEvents.scores_arrive hpre hd hf)
      change L.sharedBase + (222920 + 8 * (d.block % 2)) = L.sharedBase + 222768 at h
      omega
  case mma d =>
    have h := apart (RingEvents.query_expectTx hpre hsite hf)
    change L.sharedBase + 222776 = L.sharedBase + 222768 at h
    omega
  case tma d =>
    rcases hsite with hd | hd
    · have h := apart (RingEvents.rawReady_expectTx hpre hd hf)
      change L.sharedBase + (222808 + 8 * (d.block % 2)) = L.sharedBase + 222768 at h
      omega
    · have h := apart (RingEvents.validFree_arrive hpre hd hf)
      change L.sharedBase + (222872 + 8 * (d.block % 4)) = L.sharedBase + 222768 at h
      omega
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    have h := apart (RingEvents.validReady_arrive hpre hd hf)
    change L.sharedBase + (222840 + 8 * (d.block % 4)) = L.sharedBase + 222768 at h
    omega
  case wg2 d =>
    rcases hsite with hd | hd
    · have h := apart (RingEvents.dequantReady_arrive hpre hd hf)
      change L.sharedBase + (222792 + 8 * (d.block % 2)) = L.sharedBase + 222768 at h
      omega
    · have h := apart (RingEvents.rawFree_arrive hpre hd hf)
      change L.sharedBase + (222824 + 8 * (d.block % 2)) = L.sharedBase + 222768 at h
      omega
  all_goals exact hsite.elim

private theorem no_completion {r : Record Ref} {n : Nat} (hr : r ∈ X.objects (lastStore L cta))
    (ha : r.action = .completeTx n) : False := by
  obtain ⟨⟨g, i⟩, e, addr, sp, _, he, hk, hm, _⟩ := Protocol.object_completion_source hX hr ha
  obtain ⟨_, _, _, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g (Frame.lt_of_get hX he)).machine ht he (by
      intro f hf
      rw [hk] at hf
      cases hf)
  rcases RingTensorEvents.issue_source hpre hf hk with hq | ⟨d, _, _, _, _, _, hraw, _⟩
  · have ho := congrArg Loc.addr (hm.symm.trans hq)
    change L.sharedBase + 222768 = L.sharedBase + 222776 at ho
    omega
  · have ho := congrArg Loc.addr (hm.symm.trans hraw)
    change L.sharedBase + 222768 = L.sharedBase + (222808 + 8 * (d.block % 2)) at ho
    omega

private theorem arrival_record {r : Record Ref} {count tx : Nat}
    (hr : r ∈ X.objects (lastStore L cta)) (ha : r.action = .arrive count tx) :
    count = 1 ∧ tx = 0 ∧ ∃ g i e d, r.id = .thread (g, i) ∧
      X.get (g, i) = some e ∧ e.counts = true ∧ ctaOf L g = cta ∧ tidOf L g < 128 ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
      d.site = .lastStore ∧ d.sub = 0 := by
  cases record_source hX.tma.2.2.1 hr with
  | arrive hid he ha' =>
    obtain ⟨rfl, rfl⟩ := Action.arrive.inj (ha.symm.trans ha')
    obtain ⟨hn, hTx, hc, hTid, d, hState, hd, hSub⟩ :=
      last_store_source hpre hX hs ht he rfl
    exact ⟨hn, hTx, _, _, _, d, hid, he, rfl, hc, hTid, hState, hd, hSub⟩
  | commit _ he hm _ =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨_, _, _, hf⟩ := RingSourceSites.fired_from_trace hX (hs _ hg).machine ht he (by simp)
    obtain ⟨_, q, _, hq⟩ := RingCommitEvents.commit_source hpre hg hf rfl hm
    rcases hq with ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, hm⟩
    all_goals have hAddr := congrArg Loc.addr hm
    · change L.sharedBase + 222768 = L.sharedBase + 222784 at hAddr
      omega
    · change L.sharedBase + 222768 = L.sharedBase + (222904 + 8 * (q.i % 2)) at hAddr
      omega
    · change L.sharedBase + 222768 = L.sharedBase + (222936 + 8 * (q.i % 2)) at hAddr
      omega
  | arriveOn _ he _ _ _ => exact (Protocol.no_async_arrive hX he rfl).elim
  | init _ _ h | inval _ _ h | wait _ _ h | increment _ _ h
  | tensor _ _ _ h | bulk _ _ _ _ h | clc _ _ _ _ h =>
    rw [ha] at h
    cases h

private theorem init_first (cta : Nat) :
    PairTmaRing.InitFirst X (lastStore L cta) 128 := by
  obtain ⟨init, hSites⟩ := Protocol.IndexRing.exists_init_sites hpre hX
    (fun g hg => (hs g hg).machine) ht
  apply Protocol.IndexRing.published_init_first hX hSites cta (0 : Fin 23)
  intro r hr hn
  rcases mbar_record_published hpre hX hs ht hr with ⟨⟨n, hn'⟩, _⟩ | ⟨i, n, hi, _, hp, _⟩
  · exact (hn n hn').elim
  obtain ⟨tag, he⟩ := hi
  obtain ⟨rfl, rfl⟩ := hSites 0 cta i tag n trivial he
  exact ⟨⟨tag, he⟩, hp⟩

private theorem arrival_unique {r q : Record Ref} {n tx n' tx' : Nat}
    (hr : r ∈ X.objects (lastStore L cta)) (hq : q ∈ X.objects (lastStore L cta))
    (ha : r.action = .arrive n tx) (hb : q.action = .arrive n' tx')
    (hTid : tidOf L r.id.issuer.1 = tidOf L q.id.issuer.1) : r.id = q.id := by
  obtain ⟨_, _, g, i, e, d, hId, he, hCount, hc, _, hState, hd, hSub⟩ :=
    arrival_record hpre hX hs ht hr ha
  obtain ⟨_, _, g', j, e', d', hId', he', hCount', hc', _, hState', hd', hSub'⟩ :=
    arrival_record hpre hX hs ht hq hb
  have hg : g = g' := by
    rw [hId, hId'] at hTid
    change tidOf L g = tidOf L g' at hTid
    simp only [tidOf_eq hpre] at hTid
    simp only [ctaOf, hpre.block] at hc hc'
    omega
  subst g'
  have hRank : Bound.rank P L g (.wg0 d) = Bound.rank P L g (.wg0 d') := by
    simp [Bound.rank, Bound.wg0Rank, Bound.wg0Ordinal, Bound.wg0Block, hd, hd', hSub, hSub']
  have hSound := (hs g (Frame.lt_of_get hX he)).machine
  have nij : ¬ i < j := by
    intro hl
    have h := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX hSound ht he hCount
      (len_of_get he').le hState hState' hl
    omega
  have nji : ¬ j < i := by
    intro hl
    have h := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX hSound ht he' hCount'
      (len_of_get he).le hState' hState hl
    omega
  have hEq : i = j := by omega
  rw [hId, hId', hEq]

/-- The last-store barrier has at most one valid unit arrival from each softmax lane. -/
theorem mbar_last_store_clean {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects ⟨.shared, cta, L.sharedBase + 222768⟩) :
    r.fault = none := by
  let m := lastStore L cta
  have hFirst := init_first hpre hX hs ht cta
  have hNoInv := Protocol.objects_single_lifetime hX m
  have hComp : ∀ q ∈ X.objects m, ∀ n, q.action ≠ .completeTx n :=
    fun q hq n h => no_completion hpre hX hs ht hq h
  cases ha : r.action with
  | init n => exact mbar_init_clean hpre hX hs ht hr ha
  | pollParity p ok => exact mbar_poll_clean hpre hX hs ht hr ha
  | inval => exact (mbar_record_not_inval hX hr ha).elim
  | increment =>
    cases record_source hX.tma.2.2.1 hr with
    | increment _ he _ => exact (Protocol.no_async_arrive hX he rfl).elim
    | init _ _ h | arrive _ _ h | wait _ _ h | inval _ _ h | tensor _ _ _ h
    | arriveOn _ _ _ _ h | bulk _ _ _ _ h | commit _ _ _ h | clc _ _ _ _ h =>
      rw [ha] at h
      cases h
  | completeTx n => exact (hComp r hr n ha).elim
  | arrive n tx =>
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    have hCh := X.objects_checked hX m
    let lanes := Finset.range 128
    let label : Ref → Nat × Nat := fun ref => (tidOf L ref.issuer.1, 0)
    have hValid := hCh.gated_arrive hNoInv lanes label
      (fun i st hi hst => ⟨by
        simpa [lanes] using PairTmaRing.expected_of_init hX hFirst hNoInv hst,
        MbarRing.tx_zero_of hX hNoInv
          (fun q hq n tx h => (arrival_record hpre hX hs ht hq h).2.1) hComp hi hst⟩)
      (fun i q n tx hi hAct => by
        obtain ⟨_, st, hSt, _⟩ := PairTmaRing.state_of_init hX hFirst hNoInv hi (by simp [hAct])
        exact ⟨st, hSt⟩)
      (fun i q n tx hi hAct => by
        obtain ⟨hn, hTx, g, _, _, _, hId, _, _, _, hTid, _⟩ :=
          arrival_record hpre hX hs ht (List.mem_of_getElem? hi) hAct
        refine ⟨hn, hTx, ?_⟩
        simpa [lanes, label, hId, Ref.issuer] using hTid)
      (fun i j q q' c tx c' tx' hi hj ha ha' hLabel => by
        have hTid := congrArg Prod.fst hLabel
        exact ObjectInit.checked_record_index_eq hCh hi hj (arrival_unique hpre hX hs ht
          (List.mem_of_getElem? hi) (List.mem_of_getElem? hj) ha ha' hTid))
      (fun _ _ _ _ _ _ h => by simp [label] at h)
      (Protocol.objects_no_pending_increment hX m)
    exact (hValid k r n tx hk ha).1

/-- Once every softmax lane has arrived, the last-store object's final phase is one. -/
theorem last_store_phase_of_all_arrivals
    (hAll : ∀ k : Fin 128, ∃ i tag, X.get (cta * L.block + k.val, i) = some
      ⟨tag, .arrive ⟨.shared, cta, L.sharedBase + 222768⟩ 0 1 true .cta⟩) :
    ∃ st, stateBefore (X.objects ⟨.shared, cta, L.sharedBase + 222768⟩)
      (X.objects ⟨.shared, cta, L.sharedBase + 222768⟩).length = some st ∧ st.phase = 1 := by
  classical
  let m := lastStore L cta
  let log := X.objects m
  let ids := ((log.filter countedArrive).map Record.id).toFinset
  let threadRef (k : Fin 128) := Ref.thread (cta * L.block + k.val, (hAll k).choose)
  have hCh := X.objects_checked hX m
  have hNoInv := Protocol.objects_single_lifetime hX m
  have hIn (k : Fin 128) : threadRef k ∈ ids := by
    obtain ⟨tag, hEvent⟩ := (hAll k).choose_spec
    have hAct : objectAction X X.async m (threadRef k) = some (.arrive 1 0) := by
      simp [threadRef, objectAction, hEvent, m]
    obtain ⟨r, hr, hId⟩ := (hX.tma.2.2.1 m).2.2 _ _ hAct
    have hAction := ((hX.tma.2.2.1 m).2.1 r hr).1
    rw [hId, hAct] at hAction
    have hCount := countedArrive_iff.mpr ⟨mbar_last_store_clean hpre hX hs ht hr, 1, 0,
      (Option.some.inj hAction).symm⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, hCount⟩, hId⟩)
  have hInj : Function.Injective threadRef := by
    intro k k' he
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Prod.fst (Ref.thread.inj he))
  have hLower : 128 ≤ ids.card := by
    simpa using Finset.card_le_card_of_injOn (s := Finset.univ) threadRef
      (fun k _ => hIn k) hInj.injOn
  have hRecord {id : Ref} (hi : id ∈ ids) :
      ∃ r ∈ log, ∃ n tx, r.action = .arrive n tx ∧ r.id = id := by
    obtain ⟨r, hr, hId⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    obtain ⟨hr, hCount⟩ := List.mem_filter.mp hr
    obtain ⟨_, n, tx, hAct⟩ := countedArrive_iff.mp hCount
    exact ⟨r, hr, n, tx, hAct, hId⟩
  let laneOfRef := fun ref : Ref => tidOf L ref.issuer.1
  have hUpper : ids.card ≤ 128 := by
    have hInside : ∀ id ∈ ids, laneOfRef id ∈ Finset.range 128 := by
      intro id hi
      obtain ⟨r, hr, n, tx, hAct, rfl⟩ := hRecord hi
      obtain ⟨_, _, g, i, _, _, hId, _, _, _, hTid, _⟩ := arrival_record hpre hX hs ht hr hAct
      simpa [Finset.mem_range, laneOfRef, hId, Ref.issuer] using hTid
    have hInj : Set.InjOn laneOfRef ids := by
      intro id hi id' hi' he
      obtain ⟨r, hr, n, tx, hAct, rfl⟩ := hRecord hi
      obtain ⟨r', hr', n', tx', hAct', rfl⟩ := hRecord hi'
      exact arrival_unique hpre hX hs ht hr hr' hAct hAct' he
    simpa using Finset.card_le_card_of_injOn laneOfRef hInside hInj
  have hUnits : arrivalUnits log = 128 := by
    have hNd := hCh.1.sublist ((List.filter_sublist (p := countedArrive) (l := log)).map _)
    have hIdCount : ids.card = (log.filter countedArrive).length := by
      dsimp only [ids]
      rw [List.toFinset_card_of_nodup hNd, List.length_map]
    rw [arrivalUnits_eq_length (fun r hr _ _ _ h => (arrival_record hpre hX hs ht hr h).1),
      ← hIdCount]
    omega
  obtain ⟨r, hr, _, _, _, _⟩ := hRecord (hIn 0)
  have hInit := init_first hpre hX hs ht cta
  obtain ⟨r0, hInitRec, hAction, _, _⟩ := hInit r hr
  obtain ⟨st, hState⟩ := stateBefore_length_some hCh hNoInv (List.mem_of_getElem? hInitRec)
    hAction (by decide : validCount 128)
  have hExpected := PairTmaRing.expected_of_init hX hInit hNoInv hState
  have hTx := MbarRing.tx_zero_of hX hNoInv
    (fun q hq n tx ha => (arrival_record hpre hX hs ht hq ha).2.1)
    (fun q hq n ha => no_completion hpre hX hs ht hq ha) (le_refl log.length) hState
  have hInc := Protocol.objects_no_pending_increment hX m
  have hStrict := MbarRing.Blocker.units_lt hCh hNoInv hState hTx hInc
  obtain ⟨hPending, hAccounting⟩ := (hCh.accounted hNoInv (le_refl log.length)).2 st hState
  change arrivalUnits (log.take log.length) + st.pending = _ at hAccounting
  rw [List.take_length, hUnits, hInc, hExpected] at hAccounting
  rw [hInc, hExpected] at hPending
  rw [hUnits, hExpected] at hStrict
  exact ⟨st, hState, by omega⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
